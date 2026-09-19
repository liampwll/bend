// Why3 translation and proof elaboration. Standalone exports contain only
// goals. Normal checking admits Valid results as opaque theorem constants
// through the kernel's native-definition interface; only previously verified
// theorems may become hypotheses. The kernel itself remains unchanged.

import * as child from "node:child_process";
import * as crypto from "node:crypto";
import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import * as Bend from "./bend.ts";

type Term = Bend.HTerm;
type Data = Extract<Term, { $: "ADT" }>;
type Variable = Extract<Term, { $: "Var" }>;
type Binding = { name: string; type: Term };
type Context = Map<number, Binding>;
type Field = { type: Term; name: string };
type Constructor = { name: string; fields: Field[] };
type Datatype = { name: string; term: Data; ctors: Map<string, Constructor> };
type Signature = { name: string; params: Term[]; types: Term[]; result: Term };
type Constant = { term: Term; key: string; size: number };
type Trust = Pick<ReadonlySet<string>, "has">;

export type Goal = { name: string; id: string; file?: string; line?: number };
export type Export = { source: string; goals: Goal[]; assumptions: string[] };
export type ExportOptions = {
  laws?: string[];
  // Canonical namespaces from book_load, used only for source diagnostics.
  files?: Map<string, string | null>;
  induct?: string[];
};
export type ProveOptions = {
  binary?: string;
  config?: string;
  provers?: string[];
  timeout?: number;
  // Maximum simultaneous Why3/prover attempts, shared across obligations.
  jobs?: number;
};
export type Attempt = { prover: string; answer: string; time: number };
export type Result = { goal: Goal; valid: boolean; attempts: Attempt[] };
export type Evidence = Result & { digest: string; assumptions: string[]; source: string };
export type CheckOptions = ProveOptions & Pick<ExportOptions, "files" | "induct"> & {
  kernelOnly?: boolean;
};

class Unsupported extends Error {}
class SpecializationLimit extends Error {}

// Source positions share one line index for the duration of a check. Splitting
// every growing source prefix for every goal otherwise becomes quadratic.
class SourceLines {
  sources = new Map<string, number[]>();
  line(span: Bend.Span): number {
    let starts = this.sources.get(span.src);
    if (!starts) {
      starts = [0];
      for (let i = span.src.indexOf("\n"); i >= 0; i = span.src.indexOf("\n", i + 1)) starts.push(i + 1);
      this.sources.set(span.src, starts);
    }
    let lo = 0, hi = starts.length;
    while (lo < hi) {
      const mid = (lo + hi) >>> 1;
      if (starts[mid] <= span.beg) lo = mid + 1; else hi = mid;
    }
    return lo;
  }
}

const U32_OPS = new Set(["inc", "add", "sub", "mul", "not", "and", "or", "xor",
  "shl", "shr", "div", "mod", "is_eq", "is_ne", "is_lt", "is_le", "is_gt", "is_ge"]);

// Escape the escape character as well: a.b and a_2e_b must stay distinct.
function ident(prefix: string, name: string): string {
  return prefix + Array.from(name, (c) => /[a-zA-Z0-9]/.test(c)
    ? c : "_" + c.codePointAt(0)!.toString(16) + "_").join("");
}

function apply(f: Term, xs: Term[]): Term {
  return xs.reduce((f, x) => Bend.App(f, x), f);
}

class Translator {
  book: Bend.Book;
  options: ExportOptions;
  data = new Map<string, Datatype>();
  functions = new Map<string, Signature>();
  definitions: string[] = [];
  fresh = 0;
  fuel = 200000;
  current = "";
  hasBV = false;
  base: boolean;
  induction = new Set<string>();
  trusted: Trust;
  readonly lines: SourceLines;
  origins = new Map<string, Goal>();
  specializing = new Map<string, { key: string; weight: number }[]>();
  constants = new WeakMap<Term, Constant | null>();
  constantNormals = new WeakMap<Term, Term>();
  constantDepth = 0;
  constantFuel = 2000000;
  stableParams = new Map<string, Set<number>>();

  constructor(book: Bend.Book, options: ExportOptions, trusted: Trust = new Set<string>(), lines = new SourceLines()) {
    this.book = book;
    this.options = options;
    this.trusted = trusted;
    this.lines = lines;
    const nat = book.tlds["Nat.add"];
    this.base = nat?.$ === "Def" && nat.b === true && nat.v !== null
      && !trusted.has("Nat.add") && !certified.get(book)?.has("Nat.add");
  }

  fail(message: string, at?: Term): never {
    const where = this.location(this.current, at?.s);
    throw new Unsupported("Why3: " + (where.file ?? this.current)
      + (where.line === undefined ? "" : ":" + where.line)
      + ": " + message);
  }

  tick(): void {
    if (this.constantDepth > 0) {
      if (--this.constantFuel < 0) throw new SpecializationLimit();
      return;
    }
    if (--this.fuel < 0) {
      this.fail("translation limit reached (expanding or dependent definitions)");
    }
  }

  location(name: string, span?: Bend.Span): Goal {
    const origin = this.origins.get(name);
    if (origin) return { ...origin, name, id: ident("Law_", name) };
    let file: string | undefined;
    let longest = -1;
    const base_file = Bend.BASE_BEND;
    const def = this.book.tlds[name];
    if (def?.$ === "Def" && def.b) file = base_file;
    for (const [f, ns] of this.options.files ?? []) {
      if (ns !== null && (ns === "" || name.startsWith(ns + "."))
        && ns.length > longest && f !== base_file && !(def?.$ === "Def" && def.b)) {
        file = f;
        longest = ns.length;
      }
    }
    return { name, id: ident("Law_", name), file,
      line: span === undefined ? undefined : this.lines.line(span) };
  }

  definition(name: string): Bend.Def {
    const def = this.book.tlds[name];
    if (def?.$ !== "Def") this.fail("expected a definition: " + name);
    if (def.u) this.fail("@unsafe dependency " + name);
    if (def.i) this.fail("foreign/IO dependency " + name);
    if (def.v === null && !this.trusted.has(name)) this.fail("unfilled computational dependency " + name);
    return def;
  }

  // Audit before beta reduction: an ignored argument can still contain an
  // unsafe call or an open computation. Reducing it away must not certify it.
  audit(term: Term, seen: Set<string>, evidence = false): void {
    this.tick();
    const walk = (t: Term) => this.audit(t, seen, evidence);
    switch (term.$) {
      case "Ref":
      case "ADT": {
        if (term.$ === "ADT") term.x.forEach(walk);
        if (seen.has(term.k)) return;
        seen.add(term.k);
        const d = this.book.tlds[term.k];
        if (d?.$ === "Def") {
          this.definition(term.k);
          if (!(this.base && d.b && term.k.startsWith("U32.") && U32_OPS.has(term.k.slice(4)))) {
            walk(d.T);
            if (d.v !== null) walk(d.v);
          }
        } else if (d?.$ === "ADT") {
          walk(d.T);
          d.c.forEach((c) => walk(c.T));
        }
        return;
      }
      case "Var": if (term.v !== undefined) walk(term.v); return;
      case "Ann": walk(term.T); walk(term.x); return;
      case "All": walk(term.A); walk(term.B(Bend.Var(term.k, this.fresh++))); return;
      case "Lam": walk(term.f(Bend.Var(term.k, this.fresh++))); return;
      case "App": walk(term.f); walk(term.x); return;
      case "Let":
        term.v.forEach(walk);
        walk(term.f(term.k.map((k) => Bend.Var(k, this.fresh++))));
        return;
      case "Ctr": term.x.forEach(walk); return;
      case "Mat": walk(term.h); walk(term.m); return;
      case "Eql": walk(term.T); walk(term.a); walk(term.b); return;
      case "Typ": walk(term.g); return;
      case "Min": walk(term.a); walk(term.b); return;
      case "Rwt":
        if (!evidence) this.fail("proof rewrites in computational dependencies are not supported", term);
        walk(term.e); walk(term.p); walk(term.f); return;
      case "Hol": this.fail("TODO holes are not supported", term);
      case "Sub": this.fail("unresolved substitution", term);
    }
  }

  // Expression reduction, type unfolding and audited constant evaluation use
  // the same reducer, with separate finite budgets for optional specialization.
  normal(term: Term, unfold = false): Term {
    this.tick();
    const memo = unfold && this.constantDepth > 0 ? this.constantNormals : undefined;
    const pending: Term[] = [];
    const finish = (value: Term): Term => {
      for (const t of pending) memo!.set(t, value);
      return value;
    };
    let t = term;
    for (;;) {
      this.tick();
      if (memo) {
        const cached = memo.get(t);
        if (cached !== undefined) return finish(cached);
        pending.push(t);
      }
      if (t.$ === "Ann") { t = t.x; continue; }
      if (t.$ === "Var" && t.v !== undefined) { t = t.v; continue; }
      if (t.$ === "Let") { t = t.f(t.v); continue; }
      if (t.$ === "Ref") {
        const d = this.book.tlds[t.k];
        if (d?.$ === "ADT" && d.n === 0) return finish(Bend.ADT(t.k, [], t.s));
        if (unfold && d?.$ === "Def") {
          const def = this.definition(t.k);
          if (def.v === null) return finish(t);
          t = def.v; continue;
        }
      }
      if (t.$ === "App") {
        const f = this.normal(t.f, unfold);
        if (f.$ === "Lam") { t = f.f(t.x); continue; }
        if (f.$ === "Mat") {
          const x = this.normal(t.x, unfold);
          if (x.$ === "Ctr") {
            t = f.k === x.k ? apply(f.h, x.x) : Bend.App(f.m, t.x);
            continue;
          }
        }
        return finish({ ...t, f });
      }
      return finish(t);
    }
  }

  variable(k: string, type: Term, ctx: Context): Variable {
    const i = this.fresh++;
    const v: Variable = { $: "Var", k, i };
    ctx.set(i, { name: ident("v" + i + "_", k), type });
    return v;
  }

  key(term: Term): string {
    const t = this.normal(term, true);
    switch (t.$) {
      case "ADT": return t.k + "<" + t.x.map((x) => this.key(x)).join(",") + ">";
      case "Qua": return "&" + t.q.$;
      // Constant type families, e.g. the second parameter of a plain pair.
      case "Lam": return "lambda:" + this.key(t.f(Bend.Var("dependent", this.fresh++)));
      default: return this.fail("expected a closed first-order type; found " + t.$, t);
    }
  }

  as_data(term: Term): Data {
    const t = this.normal(term, true);
    if (t.$ !== "ADT" || t.r.length !== 0) {
      this.fail("dependent, higher-order, or residual types are not supported", t);
    }
    return t;
  }

  type(term: Term): string {
    const t = this.as_data(term);
    if (this.base && t.k === "U32") { this.hasBV = true; return "BV32.t"; }
    if (this.base && t.k === "Bool") return "bool";
    if (this.base && ["F32", "Array", "IO.OP"].includes(t.k)) {
      this.fail(t.k + " is outside the Why3 proof subset", t);
    }
    return this.datatype(t).name;
  }

  datatype(t: Data): Datatype {
    const key = this.key(t);
    const old = this.data.get(key);
    if (old) return old;
    if (this.data.size >= 256) this.fail("too many datatype specializations", t);
    const adt = this.book.tlds[t.k];
    if (adt?.$ !== "ADT" || adt.c.length === 0) {
      this.fail("empty or opaque type in a data position: " + t.k, t);
    }
    const entry: Datatype = { name: ident("t" + this.data.size + "_", t.k),
      term: t, ctors: new Map() };
    this.data.set(key, entry);
    for (const ctr of adt.c) {
      let tel = ctr.T;
      for (const x of t.x) {
        const a = this.normal(tel, true);
        if (a.$ !== "All") this.fail("invalid constructor telescope", tel);
        tel = a.B(x);
      }
      const fields: Field[] = [];
      for (let j = 0; j < ctr.n; j++) {
        const a = this.normal(tel, true);
        if (a.$ !== "All" || a.q.$ === "None") {
          this.fail("erased or dependent constructor fields: " + ctr.k, tel);
        }
        // Resolving the field now rejects negative (function-valued) types,
        // proof fields, and fields depending on an earlier value field.
        const name = this.type(a.A);
        fields.push({ type: a.A, name });
        tel = a.B(Bend.Var(a.k, this.fresh++));
      }
      entry.ctors.set(ctr.k, { name: ident("C_" + entry.name + "_", ctr.k), fields });
    }
    return entry;
  }

  // Checked expressions carry annotations, including match scrutinees and lets.
  infer(term: Term, ctx: Context): Term {
    this.tick();
    if (term.$ === "Ann") return term.T;
    if (term.$ === "Var" && term.v !== undefined) return this.infer(term.v, ctx);
    if (term.$ === "Var") {
      const b = ctx.get(term.i);
      if (b) return b.type;
    }
    if (term.$ === "Ref") {
      const d = this.book.tlds[term.k];
      if (d) return d.T;
    }
    if (term.$ === "App") {
      const f = this.normal(this.infer(term.f, ctx), true);
      if (f.$ === "All") return f.B(term.x);
    }
    if (term.$ === "Ctr") {
      const family = Bend.book_fam(this.book, term.k);
      const d = this.book.tlds[family];
      if (d?.$ === "ADT" && d.n === 0) return Bend.ADT(family, []);
    }
    this.fail("cannot infer a first-order expression (" + term.$ + ")", term);
  }

  spine(term: Term): [Term, Term[]] {
    const xs: Term[] = [];
    let t = term;
    for (;;) {
      // Preserve argument annotations while opening the application spine.
      while (t.$ === "Ann" || (t.$ === "Var" && t.v !== undefined)) {
        t = t.$ === "Ann" ? t.x : t.v!;
      }
      if (t.$ !== "App") return [t, xs.reverse()];
      xs.push(t.x);
      t = t.f;
    }
  }

  expr(term: Term, expected: Term, ctx: Context): string {
    this.tick();
    if (term.$ === "Ann") return this.expr(term.x, term.T, ctx);
    if (term.$ === "Var" && term.v !== undefined) return this.expr(term.v, expected, ctx);
    if (term.$ === "Let") return this.let(term, [], expected, ctx);
    const [head, args] = this.spine(term);
    if (head.$ === "Lam" && args.length > 0) {
      return this.expr(apply(head.f(args[0]), args.slice(1)), expected, ctx);
    }
    if (head.$ === "Let" && args.length > 0) {
      // The let's result is a function (a flattened match continuation).
      return this.let(head, args, expected, ctx);
    }
    if (head.$ === "Mat" && args.length > 0) {
      return this.match(head, args, expected, ctx);
    }
    if (head.$ === "Ref") return this.call(head.k, args, ctx);
    if (args.length > 0) this.fail("higher-order application", head);
    if (head.$ === "Var") {
      const v = ctx.get(head.i);
      if (v) return v.name;
      this.fail("proof-dependent or unbound variable " + head.k, head);
    }
    if (head.$ === "Ctr") {
      const t = this.as_data(expected);
      if (this.base && t.k === "Bool") return head.k;
      if (this.base && t.k === "U32") return this.word(head);
      const ctr = this.datatype(t).ctors.get(head.k);
      if (!ctr || ctr.fields.length !== head.x.length) this.fail("invalid constructor", head);
      const xs = head.x.map((x, i) => this.expr(x, ctr.fields[i].type, ctx));
      return "(" + [ctr.name, ...xs].join(" ") + ")";
    }
    this.fail("unsupported expression " + head.$ + " (proof rewrites and effects are not erased)", head);
  }

  let(term: Extract<Term, { $: "Let" }>, args: Term[], expected: Term, ctx: Context): string {
    const inner = new Map(ctx);
    const vs = term.v.map((v, j) => this.variable(term.k[j], this.infer(v, ctx), inner));
    const values = term.v.map((v, j) => this.expr(v, inner.get(vs[j].i)!.type, ctx));
    let body = this.expr(apply(term.f(vs), args), expected, inner);
    for (let j = vs.length - 1; j >= 0; j--) {
      body = "(let " + inner.get(vs[j].i)!.name + " = " + values[j] + " in " + body + ")";
    }
    return body;
  }

  word(term: Extract<Term, { $: "Ctr" }>): string {
    this.hasBV = true;
    let t = term.x[0];
    let n = 0n;
    for (let i = 0; i < 32; i++) {
      const c = this.normal(t);
      if (c.$ !== "Ctr" || c.k !== "WCon") this.fail("only literal U32 constructors are supported", term);
      const b = this.normal(c.x[0]);
      if (b.$ !== "Ctr" || !["False", "True"].includes(b.k)) {
        this.fail("only literal U32 constructors are supported", term);
      }
      if (b.k === "True") n |= 1n << BigInt(i);
      t = c.x[1];
    }
    const end = this.normal(t);
    if (end.$ !== "Ctr" || end.k !== "WNil") this.fail("invalid U32 literal", term);
    // A typed literal maps directly to a solver bitvector, avoiding quantified
    // integer-conversion axioms. The decoded word is already in U32's range.
    return "(" + n.toString() + " : BV32.t)";
  }

  match(head: Extract<Term, { $: "Mat" }>, args: Term[], expected: Term, ctx: Context): string {
    const type = this.as_data(this.infer(args[0], ctx));
    if (this.base && type.k === "U32") this.fail("matching U32's Word representation is not supported", head);
    const value = this.normal(args[0]);
    if (value.$ === "Ctr") {
      return this.expr(head.k === value.k ? apply(head.h, [...value.x, ...args.slice(1)])
        : apply(head.m, args), expected, ctx);
    }
    const bool = this.base && type.k === "Bool";
    const ctors = bool ? new Map<string, Constructor>([
      ["False", { name: "False", fields: [] }], ["True", { name: "True", fields: [] }],
    ]) : this.datatype(type).ctors;
    const remaining = new Set(ctors.keys());
    const arms: string[] = [];
    let branch: Term = head;
    while (remaining.size > 0) {
      branch = this.normal(branch);
      if (branch.$ !== "Mat") {
        if (branch.$ === "Efq") this.fail("empty elimination without an empty match", branch);
        arms.push("| _ -> " + this.expr(apply(branch, args), expected, ctx));
        remaining.clear();
        break;
      }
      const ctr = ctors.get(branch.k);
      if (!ctr || !remaining.delete(branch.k)) this.fail("invalid match constructor " + branch.k, branch);
      const inner = new Map(ctx);
      const vars = ctr.fields.map((f, i) => this.variable("field" + i, f.type, inner));
      const names = vars.map((v) => inner.get(v.i)!.name);
      const body = apply(branch.h, [...vars, ...args.slice(1)]);
      arms.push("| " + [ctr.name, ...names].join(" ") + " -> " + this.expr(body, expected, inner));
      branch = branch.m;
    }
    return "(match " + this.expr(args[0], type, ctx) + " with " + arms.join(" ") + " end)";
  }

  intrinsic(name: string, xs: Term[], ctx: Context): string | null {
    const d = this.book.tlds[name];
    if (!this.base || d?.$ !== "Def" || !d.b || !name.startsWith("U32.")) return null;
    const op = name.slice(4);
    const binary: Record<string, string> = { add: "add", sub: "sub", mul: "mul",
      and: "bw_and", or: "bw_or", xor: "bw_xor" };
    const comparisons: Record<string, string> = { is_eq: "=", is_ne: "<>",
      is_lt: "BV32.ult", is_le: "BV32.ule", is_gt: "BV32.ugt", is_ge: "BV32.uge" };
    const unary = ["inc", "not", "shl", "shr"];
    if (!U32_OPS.has(op)) return null;
    if (xs.length !== (unary.includes(op) ? 1 : 2)) this.fail("partially applied " + name);
    this.hasBV = true;
    const vs = xs.map((x) => this.expr(x, Bend.ADT("U32", []), ctx));
    const [a, b] = vs;
    if (op in binary) return "(BV32." + binary[op] + " " + vs.join(" ") + ")";
    if (op in comparisons) {
      const p = comparisons[op];
      return "(if " + (p.startsWith("BV32.") ? p + " " + a + " " + b : a + " " + p + " " + b)
        + " then True else False)";
    }
    if (op === "inc") return "(BV32.add " + a + " (1 : BV32.t))";
    if (op === "not") return "(BV32.bw_not " + a + ")";
    if (op === "shl" || op === "shr") return "(BV32." + (op === "shl" ? "lsl_bv" : "lsr_bv")
      + " " + a + " (1 : BV32.t))";
    // Bend explicitly defines x / 0 = 0 and x % 0 = x.
    return "(if " + b + " = (0 : BV32.t) then " + (op === "div" ? "(0 : BV32.t)" : a)
      + " else BV32." + (op === "div" ? "udiv" : "urem") + " " + a + " " + b + ")";
  }

  // Specialize closed constructor arguments, just as we specialize erased type
  // arguments. In particular, comparisons with fixed Peano bounds then become
  // finite case distinctions instead of quantified recursive SMT definitions.
  constant(term: Term, budget = { left: 16000 }): Constant | null {
    const cached = this.constants.get(term);
    if (cached !== undefined) return cached;
    if (--budget.left < 0 || this.constantDepth >= 256 || this.constantFuel <= 0) return null;
    this.constantDepth++;
    let result: Constant | null = null;
    try {
      const t = this.normal(term, true);
      if (t.$ !== "Ctr") return null;
      const xs: Constant[] = [];
      for (const x of t.x) {
        const c = this.constant(x, budget);
        if (c === null) return null;
        xs.push(c);
      }
      result = { term: { ...t, x: xs.map((x) => x.term) },
        key: JSON.stringify(t.k) + "[" + xs.map((x) => x.key).join(",") + "]",
        size: 1 + xs.reduce((n, x) => n + x.size, 0) };
      this.constants.set(result.term, result);
      return result;
    } catch (e) {
      if (!(e instanceof SpecializationLimit)) throw e;
      return null;
    } finally {
      this.constantDepth--;
      this.constants.set(term, result);
    }
  }

  // Keep invariant recursive parameters generic. Otherwise e.g. add(n, 0)
  // gets a different symbol from add(n, m), obscuring earlier addition lemmas.
  stable_parameters(name: string, def: Bend.Def, arity: number): Set<number> {
    const key = JSON.stringify([name, arity]);
    const cached = this.stableParams.get(key);
    if (cached) return cached;
    const formals = Array.from({ length: arity }, (_, i): Term => Bend.Var("parameter" + i, this.fresh++));
    const stable = new Set(formals.map((_, i) => i));
    let recursive = false;
    const scan = (term: Term): void => {
      this.tick();
      const t = this.normal(term);
      const [h, args] = this.spine(t);
      if (h.$ === "Ref" && h.k === name && args.length === arity) {
        recursive = true;
        args.forEach((a, i) => {
          const v = this.normal(a);
          if (v.$ !== "Var" || v.i !== (formals[i] as Variable).i) stable.delete(i);
        });
      }
      if (h.$ === "Mat" && args.length > 0) {
        // A leading match is a function binder too. Apply the remaining
        // arguments in every arm, so invariant parameters retain identities.
        const fields = Array.from({ length: this.book.ctrs[h.k].n },
          (_, i): Term => Bend.Var("field" + i, this.fresh++));
        scan(apply(h.h, [...fields, ...args.slice(1)]));
        scan(apply(h.m, args));
        return;
      }
      if (h.$ === "Lam" && args.length === 0) {
        scan(h.f(Bend.Var("argument", this.fresh++)));
      }
      if (h.$ === "Ctr") h.x.forEach(scan);
      args.forEach(scan);
    };
    scan(apply(def.v!, formals));
    if (!recursive) stable.clear();
    this.stableParams.set(key, stable);
    return stable;
  }

  call(name: string, args: Term[], ctx: Context): string {
    const def = this.definition(name);
    if (def.v === null) this.fail("opaque theorem used as a computational dependency: " + name);
    const native = this.intrinsic(name, args, ctx);
    if (native !== null) return native;
    const params: Term[] = [];
    const types: Term[] = [];
    const actuals: Term[] = [];
    const static_keys: string[] = [];
    const inner: Context = new Map();
    const stable = this.stable_parameters(name, def, args.length);
    const constants = args.map((a, i) => stable.has(i) ? null : this.constant(a));
    const weight = constants.reduce((n, c) => n + (c?.size ?? 0), 0);
    const constantKey = JSON.stringify(constants.map((c) => c?.key ?? null));
    const active = this.specializing.get(name) ?? [];
    // A changing static argument must shrink during recursive expansion.
    // Growing accumulators and toggling flags fall back to the generic body.
    const specialize = active.length === 0 || constantKey === active[active.length - 1].key
      || weight < active[active.length - 1].weight;
    let tel = def.T;
    for (const [index, arg] of args.entries()) {
      const t = this.normal(tel, true);
      if (t.$ !== "All") this.fail("too many arguments to " + name);
      const a = this.normal(t.A, true);
      if (a.$ === "Typ" || a.$ === "Qnt") {
        if (t.q.$ !== "None") this.fail("live type/quantity parameter in " + name);
        static_keys.push(JSON.stringify([index, "type", this.key(arg)]));
        params.push(arg);
        tel = t.B(arg);
      } else {
        if (t.q.$ === "None") this.fail("erased value/proof parameter in " + name);
        this.type(t.A);
        const c = specialize ? constants[index] : null;
        if (c !== null) {
          static_keys.push(JSON.stringify([index, "value", c.key]));
          const value = Bend.Ann(c.term, t.A);
          params.push(value);
          tel = t.B(value);
          continue;
        }
        const v = this.variable(t.k, t.A, inner);
        params.push(v);
        types.push(t.A);
        actuals.push(arg);
        tel = t.B(v);
      }
    }
    const result = this.type(tel); // Reject partial applications and dependent results.
    const key = JSON.stringify([name, static_keys]);
    let sig = this.functions.get(key);
    if (!sig) {
      if (this.functions.size >= 512) this.fail("too many function specializations");
      sig = { name: ident("f" + this.functions.size + "_", name), params, types, result: tel };
      this.functions.set(key, sig);
      const previous = this.current;
      this.current = name;
      // Reify the checker's shared type cells before specializing binders, so
      // annotations under polymorphic lambdas receive the same substitutions.
      const checked = def.e === undefined ? def.v!
        : Bend.term_higher(Bend.term_lower(Bend.term_higher(def.e)));
      this.specializing.set(name, [...active, { key: specialize ? constantKey : "generic",
        weight: specialize ? weight : 0 }]);
      let body: string;
      try {
        body = this.expr(apply(checked, params), tel, inner);
      } finally {
        if (active.length > 0) this.specializing.set(name, active);
        else this.specializing.delete(name);
      }
      const binders = [...inner.values()].map((b) => "(" + b.name + ": " + this.type(b.type) + ")");
      this.definitions.push("  function " + sig.name + " " + binders.join(" ") + ": " + result + " =\n    " + body);
      this.current = previous;
    }
    const values = actuals.map((x, i) => this.expr(x, types[i], ctx));
    return "(" + [sig.name, ...values].join(" ") + ")";
  }

  proposition(term: Term, ctx: Context): string {
    const t = this.normal(term, true);
    if (t.$ === "Eql") {
      this.type(t.T);
      return "(" + this.expr(t.a, t.T, ctx) + " = " + this.expr(t.b, t.T, ctx) + ")";
    }
    if (t.$ === "All") {
      const a = this.normal(t.A, true);
      // An erased proof argument may be supplied by a dead, unfilled claim in
      // Bend. It must never become an SMT premise. Erased data parameters are
      // safe logical quantifiers and let local automation respect affine uses.
      if (t.q.$ === "None" && this.is_proposition(a)) {
        this.fail("erased quantified proof parameters cannot be assumed", t);
      }
      // A `where` binder is a dependent pair of a value and its evidence.
      // Quantify the value and guard the conclusion by the refinement. The
      // evidence stays unavailable as a computational value.
      if (this.base && a.$ === "ADT" && a.k === "Sigma" && this.is_proposition(a)
        && !this.is_proposition(this.normal(a.x[2], true))) {
        const inner = new Map(ctx);
        const v = this.variable(t.k, a.x[2], inner);
        const type = this.type(a.x[2]);
        const premise = this.proposition(apply(a.x[3], [v]), inner);
        const pair: Term = Bend.Ctr("Tuple", [v, Bend.Var("proof", this.fresh++)]);
        return "(forall " + inner.get(v.i)!.name + ": " + type + ". (" + premise
          + " -> " + this.proposition(t.B(pair), inner) + "))";
      }
      if (this.is_proposition(a) && !(this.base && a.$ === "ADT" && a.k === "Unit")) {
        const premise = this.proposition(a, ctx);
        const body = t.B(Bend.Var("proof", this.fresh++));
        return "(" + premise + " -> " + this.proposition(body, ctx) + ")";
      }
      const type = this.type(a);
      const inner = new Map(ctx);
      const v = this.variable(t.k, a, inner);
      const mark = this.options.induct?.includes(t.k) ? " [@induction]" : "";
      if (mark) this.induction.add(t.k);
      return "(forall " + inner.get(v.i)!.name + mark + ": " + type + ". "
        + this.proposition(t.B(v), inner) + ")";
    }
    if (t.$ === "ADT" && this.empty(t)) return "false";
    if (t.$ === "ADT" && this.base) {
      if (t.k === "Unit") return "true";
      if (t.k === "Either") {
        return "(" + this.proposition(t.x[2], ctx) + " \\/ " + this.proposition(t.x[3], ctx) + ")";
      }
      if (t.k === "Sigma") {
        const a = this.normal(t.x[2], true);
        if (this.is_proposition(a)) {
          const body = apply(t.x[3], [Bend.Var("proof", this.fresh++)]);
          return "(" + this.proposition(a, ctx) + " /\\ " + this.proposition(body, ctx) + ")";
        }
        const type = this.type(a);
        const inner = new Map(ctx);
        const v = this.variable("witness", a, inner);
        return "(exists " + inner.get(v.i)!.name + ": " + type + ". "
          + this.proposition(apply(t.x[3], [v]), inner) + ")";
      }
    }
    this.fail("expected a proposition (equality, implication, conjunction, disjunction or existential); found " + t.$, t);
  }

  is_proposition(t: Term): boolean {
    this.tick();
    if (t.$ === "Eql") return true;
    if (t.$ === "All") return this.is_proposition(this.normal(t.B(Bend.Var("argument", this.fresh++)), true));
    if (t.$ !== "ADT") return false;
    if (this.empty(t)) return true;
    if (!this.base) return false;
    if (t.k === "Unit") return true;
    if (t.k === "Either") return this.is_proposition(this.normal(t.x[2], true))
      && this.is_proposition(this.normal(t.x[3], true));
    if (t.k === "Sigma") return this.is_proposition(this.normal(apply(t.x[3], [Bend.Var("witness", this.fresh++)]), true));
    return false;
  }

  empty(t: Data): boolean {
    const d = this.book.tlds[t.k];
    return d?.$ === "ADT" && d.c.length === 0;
  }

  inhabited(): void {
    const known = new Set(["bool", "BV32.t"]);
    let changed = true;
    while (changed) {
      changed = false;
      for (const d of this.data.values()) {
        if (!known.has(d.name) && [...d.ctors.values()].some((c) => c.fields.every((f) => known.has(f.name)))) {
          known.add(d.name);
          changed = true;
        }
      }
    }
    for (const d of this.data.values()) {
      if (!known.has(d.name)) this.fail("datatype has no finite inhabitants: " + d.term.k, d.term);
    }
  }

  // Start with facts whose symbols are already dependencies of the goal.
  // This avoids importing unrelated recursive theories just because their
  // lemmas precede this one. A failed focused attempt can use the full set.
  relevant(names: string[], facts: string[]): string[] {
    const refs = references;
    const needed = new Set<string>();
    const visit = (name: string): void => {
      if (needed.has(name)) return;
      needed.add(name);
      const d = this.book.tlds[name];
      if (d === undefined) return;
      for (const r of refs(d.T)) visit(r);
      if (d.$ === "Def" && d.v !== null) for (const r of refs(d.v)) visit(r);
    };
    for (const name of names) for (const r of refs(this.book.tlds[name].T)) visit(r);
    return facts.filter((name) => [...refs(this.book.tlds[name].T)].every((r) => needed.has(r)));
  }

  // Recognize universally false equalities: different constructors, or an
  // injective occurrence of a varying variable against an independent term.
  // These need local premises; speculating without them just wastes ATP time.
  needs_hypothesis(term: Term): boolean {
    try {
      const varying = new Set<number>();
      let t = this.normal(term, true);
      while (t.$ === "All") {
        const a = this.normal(t.A, true);
        if (this.is_proposition(a)) return false;
        const type = this.type(a);
        const i = this.fresh++;
        const v: Term = Bend.Var(t.k, i);
        if (type === "bool" || type === "BV32.t" || this.datatype(this.as_data(a)).ctors.size > 1) varying.add(i);
        t = this.normal(t.B(v), true);
      }
      if (t.$ !== "Eql") return false;
      this.type(t.T);
      this.inhabited();
      const a = this.normal(t.a, true), b = this.normal(t.b, true);
      if (a.$ === "Ctr" && b.$ === "Ctr" && a.k !== b.k) return true;
      const injective = (term: Term): number[] => {
        const x = this.normal(term, true);
        return x.$ === "Var" && varying.has(x.i) ? [x.i] : x.$ === "Ctr" ? x.x.flatMap(injective) : [];
      };
      const variables = (x: Term): Set<number> => {
        const ids = new Set<number>();
        syntax(Bend.term_lower(x), (v) => { if (v.$ === "Var") ids.add(v.i); return v; });
        return ids;
      };
      const left = variables(a), right = variables(b);
      return injective(a).some((i) => !right.has(i)) || injective(b).some((i) => !left.has(i));
    } catch (e) {
      if (!(e instanceof Unsupported)) throw e;
      return false;
    }
  }

  run(checked = false, facts: string[] = []): Export {
    const counts = new Map<string, number>();
    if (!this.options.laws?.length) {
      for (const name of this.book.order) counts.set(name, (counts.get(name) ?? 0) + 1);
    }
    const names = this.options.laws?.length ? [...new Set(this.options.laws)]
      : [...counts.keys()].filter((name) => {
        const d = this.book.tlds[name];
        this.current = name;
        return d.$ === "Def" && !d.b && !d.i && (d.v === null
          || (counts.get(name)! > 1 && this.is_proposition(this.normal(d.T, true))));
      });
    if (names.length === 0) this.fail("no laws selected; use --law <canonical name> for a theorem def");
    // The integrated elaborator has already checked this prefix and goal type.
    // A public standalone export always validates with the kernel itself.
    if (this.book.hols !== 0) this.fail("TODO holes are not supported; declare an unfilled law instead");
    const seen = new Set<string>();
    for (const name of names) {
      this.current = name;
      const d = this.book.tlds[name];
      if (d?.$ !== "Def") this.fail("unknown law " + name);
      if (d.u || d.i) this.fail("unsafe or foreign law " + name);
      this.audit(d.T, seen);
    }
    if (!checked) {
      this.book.open = 0;
      Bend.book_valid(this.book);
    }
    const goals: Goal[] = [];
    const formulas: string[] = [];
    const assumptions: string[] = [];
    for (const name of facts) {
      if (names.includes(name)) continue;
      // An unsupported verified theorem is irrelevant to this first-order
      // task. Roll back every bit of translator state if it cannot be used.
      const saved = { data: new Map(this.data), functions: new Map(this.functions),
        definitions: this.definitions.slice(), fresh: this.fresh, fuel: this.fuel,
        hasBV: this.hasBV, induction: new Set(this.induction) };
      try {
        this.current = name;
        const def = this.definition(name);
        this.audit(def.T, new Set());
        if (def.v !== null) this.audit(def.v, new Set([name]), true);
        const formula = this.proposition(def.T, new Map());
        this.inhabited();
        formulas.push("  (* Previously verified: " + name.replace(/\(\*|\*\)|[\r\n\0]/g, " ")
          + " *)\n  axiom " + ident("Fact_", name) + ":\n    " + formula);
        assumptions.push(name);
      } catch (e) {
        if (!(e instanceof Unsupported)) throw e;
        Object.assign(this, saved);
      }
    }
    for (const name of names) {
      this.current = name;
      const d = this.book.tlds[name];
      if (d?.$ !== "Def") this.fail("unknown law " + name);
      if (d.u || d.i) this.fail("unsafe or foreign law " + name);
      const goal = this.location(name, d.T.s);
      goals.push(goal);
      const formula = this.proposition(d.T, new Map());
      const origin = ((goal.file ?? name) + (goal.line === undefined ? "" : ":" + goal.line))
        .replace(/\(\*|\*\)|[\r\n]/g, " ");
      formulas.push("  (* " + origin + " *)\n  goal " + goal.id + ":\n    " + formula);
    }
    for (const k of this.options.induct ?? []) {
      if (!checked && !this.induction.has(k)) this.fail("no quantified data variable named " + k);
    }
    this.inhabited();
    const types = [...this.data.values()].map((d, i) =>
      "  " + (i === 0 ? "type " : "with ") + d.name + " =\n    "
      + [...d.ctors.values()].map((c) => "| " + [c.name, ...c.fields.map((f) => f.name)].join(" ")).join("\n    "));
    const source = [
      assumptions.length === 0 ? "(* Generated by Bend's Why3 backend. No laws are assumed. *)"
        : "(* Generated by Bend. Hypotheses below have already been verified. *)",
      "module Bend",
      "  use bool.Bool",
      ...(this.hasBV ? ["  use int.Int", "  use bv.BV32 as BV32"] : []),
      ...types, ...this.definitions, ...formulas, "end", "",
    ].join("\n\n");
    return { source, goals, assumptions };
  }
}

export function export_book(book: Bend.Book, options: ExportOptions = {}): Export {
  return new Translator(book, options).run();
}

// Integrated proof checking
// =========================
// The registry is per loaded book, never a disk cache or a source annotation.
// No source can request the native flag: it is installed only after Valid.
const certified = new WeakMap<Bend.Book, Map<string, Evidence>>();

export function evidence(book: Bend.Book): Evidence[] {
  return [...(certified.get(book)?.values() ?? [])];
}

export function export_session(book: Bend.Book): string {
  const tasks = evidence(book);
  return tasks.length === 0 ? "(* No ATP obligations: all proofs checked by Bend. *)\nmodule Bend\nend\n"
    : tasks.map((task, i) => task.source.replace("module Bend\n", "module Bend_" + i + "\n")).join("\n");
}

function syntax(t: Bend.LTerm, visit: (t: Bend.LTerm) => Bend.LTerm): Bend.LTerm {
  t = visit(t);
  const go = (x: Bend.LTerm) => syntax(x, visit);
  switch (t.$) {
    case "All": return { ...t, A: go(t.A), B: go(t.B) };
    case "Lam": return { ...t, f: go(t.f) };
    case "App": return { ...t, f: go(t.f), x: go(t.x) };
    case "Let": return { ...t, v: t.v.map(go), f: go(t.f) };
    case "ADT": case "Ctr": return { ...t, x: t.x.map(go) };
    case "Mat": return { ...t, h: go(t.h), m: go(t.m) };
    case "Eql": return { ...t, a: go(t.a), b: go(t.b), T: go(t.T) };
    case "Rwt": return { ...t, e: go(t.e), p: go(t.p), f: go(t.f) };
    case "Ann": return { ...t, x: go(t.x), T: go(t.T) };
    case "Typ": return { ...t, g: go(t.g) };
    case "Min": return { ...t, a: go(t.a), b: go(t.b) };
    case "Sub": return { ...t, f: go(t.f),
      v: t.v.$ === "PVar" || t.v.$ === "PCtr" ? t.v : go(t.v) };
    default: return t;
  }
}

const referenceSets = new WeakMap<Term, ReadonlySet<string>>();
const constructorSets = new WeakMap<Term, ReadonlySet<string>>();
function references(term: Term): ReadonlySet<string> {
  const old = referenceSets.get(term);
  if (old) return old;
  const names = new Set<string>();
  const constructors = new Set<string>();
  syntax(Bend.term_lower(term), (t) => {
    if (t.$ === "Ref" || t.$ === "ADT") names.add(t.k);
    if (t.$ === "Ctr" || t.$ === "Mat") constructors.add(t.k);
    return t;
  });
  referenceSets.set(term, names);
  constructorSets.set(term, constructors);
  return names;
}

// Close a local goal over the values it mentions and usable live hypotheses.
// Data arguments are erased so proving a fact never consumes an affine value;
// proof arguments remain live, and the final kernel pass checks their uses.
function close_goal(err: Bend.Err, trusted: Trust, hypotheses: boolean, book: Bend.Book, lines: SourceLines): { type: Term; args: Term[] } {
  const entries = Bend.pmap_to_array(err.ctx).sort(([a], [b]) => a - b);
  const depth = entries.length ? entries[entries.length - 1][0] + 1 : 0;
  const needed = new Set<number>();
  const collect = (t: Bend.LTerm) => syntax(t, (x) => {
    if (x.$ === "Var" && x.i >= 0 && x.i < depth) needed.add(x.i);
    return x;
  });
  let type = collect(Bend.term_lower(err.exp as Term, depth));
  const ctx: Context = new Map(entries.map(([i, a]) => [i, { name: "v" + i, type: a.T }]));
  const proofs = new Set<number>();
  for (const [i, a] of entries) {
    if (!hypotheses || a.q.$ === "None") continue;
    const tr = new Translator(book, {}, trusted, lines);
    try {
      if (!tr.is_proposition(tr.normal(a.T, true))) continue;
      tr.proposition(a.T, ctx);
      needed.add(i);
      proofs.add(i);
    } catch (e) {
      if (!(e instanceof Unsupported)) throw e;
    }
  }
  let size = -1;
  while (size !== needed.size) {
    size = needed.size;
    for (const [i, a] of entries) if (needed.has(i)) collect(Bend.term_lower(a.T, depth));
  }
  const used = entries.filter(([i]) => needed.has(i));
  for (const [i, a] of used.slice().reverse()) {
    // An erased proof that appears in the goal must fail translation, rather
    // than being promoted to a live premise by this closure conversion.
    const q = proofs.has(i) ? a.q : Bend.None();
    type = Bend.All(q, a.k, i, Bend.term_lower(a.T, depth), type, err.spn);
  }
  return { type: Bend.term_higher(type), args: used.map(([i, a]) => Bend.Var(a.k, i)) };
}

type Completed = { tld: Bend.TLD; locals: Map<string, Bend.Def>; facts: string[]; records: Map<string, Evidence> };
type Declaration = { name: string; raw: Bend.TLD; at: number; result?: Completed; work: Promise<void> };
type Fact = { name: string; at: number; refs: ReadonlySet<string> };

// One versioned context per check. Views are bounded by declaration position,
// so an asynchronous worker can never see a later definition or theorem.
class ProofContext {
  declarations: Declaration[] = [];
  versions = new Map<string, Declaration[]>();
  constructors = new Map<string, string>();
  locals = new Map<string, { at: number; tld: Bend.Def }>();
  certificates = new Map<string, number>();
  facts: Fact[] = [];
  index = new Map<string, Fact[]>();
  pending = new Map<string, Declaration[]>();

  add(decl: Declaration, automatic: boolean): void {
    this.declarations.push(decl);
    const versions = this.versions.get(decl.name) ?? [];
    versions.push(decl);
    this.versions.set(decl.name, versions);
    if (decl.raw.$ === "ADT") for (const c of decl.raw.c) this.constructors.set(c.k, decl.name);
    if (automatic) {
      const key = references(decl.raw.T).values().next().value ?? "";
      const pending = this.pending.get(key) ?? [];
      pending.push(decl);
      this.pending.set(key, pending);
    }
  }

  find(name: string, before: number): Declaration | undefined {
    const versions = this.versions.get(name);
    if (!versions) return;
    let lo = 0, hi = versions.length;
    while (lo < hi) {
      const mid = (lo + hi) >>> 1;
      if (versions[mid].at < before) lo = mid + 1; else hi = mid;
    }
    return versions[lo - 1];
  }

  get(name: string, before: number): Bend.TLD | undefined {
    const local = this.locals.get(name);
    if (local && local.at < before) return local.tld;
    const decl = this.find(name, before);
    return decl?.result?.tld ?? decl?.raw;
  }

  accept(decl: Declaration): void {
    const result = decl.result!;
    for (const [name, tld] of result.locals) this.locals.set(name, { at: decl.at, tld });
    for (const name of result.records.keys()) this.certificates.set(name, decl.at);
    for (const name of result.facts) {
      const tld = result.locals.get(name) ?? result.tld;
      const fact = { name, at: decl.at, refs: references(tld.T) };
      this.facts.push(fact);
      const key = fact.refs.values().next().value ?? "";
      const entries = this.index.get(key) ?? [];
      entries.push(fact);
      this.index.set(key, entries);
    }
  }

  view(before: number, locals = new Map<string, Bend.Def>()) {
    const book = Bend.book_nil();
    // No enumeration is needed by translation: selected laws and facts have
    // explicit names. Kernel checks use the closed slice below, never a proxy.
    book.tlds = new Proxy(Object.create(null), { get: (_, name: string) => locals.get(name) ?? this.get(name, before) });
    book.ctrs = new Proxy(Object.create(null), { get: (_, name: string) => {
      const adt = book.tlds[this.constructors.get(name) ?? ""];
      return adt?.$ === "ADT" ? adt.c.find((c) => c.k === name) : undefined;
    } });
    const trusted: Trust = { has: (name) => locals.get(name)?.b === true
      || (this.certificates.get(name) ?? Infinity) < before };
    return { book, trusted };
  }

  needed(book: Bend.Book, type: Term): Set<string> {
    const needed = new Set<string>();
    const visit = (name: string): void => {
      if (needed.has(name)) return;
      needed.add(name);
      const tld = book.tlds[name];
      if (!tld) return;
      for (const ref of references(tld.T)) visit(ref);
      if (tld.$ === "Def" && tld.v !== null) for (const ref of references(tld.v)) visit(ref);
    };
    for (const ref of references(type)) visit(ref);
    return needed;
  }

  relevant(needed: Set<string>, before: number): string[] {
    const facts = [...needed, ""].flatMap((key) => this.index.get(key) ?? []);
    return facts.filter((f) => f.at < before && [...f.refs].every((r) => needed.has(r)))
      .sort((a, b) => a.at - b.at).map((f) => f.name);
  }

  available(before: number): string[] {
    return this.facts.filter((f) => f.at < before).sort((a, b) => a.at - b.at).map((f) => f.name);
  }

  waiting(needed: Set<string>, before: number): Declaration[] {
    return [...needed, ""].flatMap((key) => this.pending.get(key) ?? [])
      .filter((d) => d.at < before && !d.result && [...references(d.raw.T)].every((r) => needed.has(r)));
  }

  // Include the transitive dependencies of types, bodies AND constructor
  // telescopes. Only earlier declarations can enter this slice. They have
  // already been checked; the unchanged kernel checks the appended root.
  validate(name: string, root: Bend.TLD, before: number, locals: Map<string, Bend.Def>, skip = false): Bend.Book {
    const slice = Bend.book_nil();
    const seen = new Set<string>([name]);
    const visit = (key: string): void => {
      if (seen.has(key)) return;
      seen.add(key);
      const tld = locals.get(key) ?? this.get(key, before);
      if (!tld) return;
      collect(tld);
      slice.tlds[key] = tld;
      slice.order.push(key);
    };
    const terms = (term: Term): void => {
      for (const key of references(term)) visit(key);
      for (const key of constructorSets.get(term)!) visit(this.constructors.get(key) ?? "");
    };
    const collect = (tld: Bend.TLD): void => {
      terms(tld.T);
      if (tld.$ === "ADT") for (const c of tld.c) terms(c.T);
      else if (tld.v !== null) terms(tld.v);
    };
    collect(root);
    slice.tlds[name] = root;
    slice.order.push(name);
    Bend.book_valid(slice, slice.order.length - (skip ? 0 : 1));
    // book_valid builds its own seen constructor table; retain one as well
    // for diagnostics and the local-goal elaborator.
    for (const tld of Object.values(slice.tlds)) if (tld.$ === "ADT") for (const c of tld.c) slice.ctrs[c.k] = c;
    return slice;
  }

  assemble(): Bend.Book {
    const book = Bend.book_nil();
    const append = (name: string, tld: Bend.TLD) => {
      book.tlds[name] = tld;
      book.order.push(name);
      if (tld.$ === "ADT") for (const c of tld.c) book.ctrs[c.k] = c;
    };
    for (const d of this.declarations) {
      d.result?.locals.forEach((tld, name) => append(name, tld));
      append(d.name, d.result?.tld ?? d.raw);
    }
    return book;
  }
}

function complete(book: Bend.Book): void {
  const n = book.hols + book.open;
  if (n > 0) throw new Error(n + " TODO" + (n === 1 ? "" : "s")
    + " found.\nThe code is incomplete, and not a valid proof yet.");
}

export async function check_book(book: Bend.Book, options: CheckOptions = {}, done = 0): Promise<void> {
  options = { ...options,
    binary: options.binary ?? process.env.BEND_WHY3,
    provers: options.provers?.length ? options.provers : process.env.BEND_WHY3_PROVERS?.split(",").filter(Boolean),
    timeout: options.timeout ?? (process.env.BEND_WHY3_TIMEOUT === undefined ? 1 : Number(process.env.BEND_WHY3_TIMEOUT)),
    jobs: options.jobs ?? (process.env.BEND_WHY3_JOBS === undefined ? undefined : Number(process.env.BEND_WHY3_JOBS)),
  };
  if (certified.has(book)) throw new Error("Why3: reload the source before checking a certified book again");
  // Explicit TODOs remain incomplete. They can never supply facts to the ATP.
  if (options.kernelOnly || book.hols > 0) {
    book.open = 0;
    Bend.book_valid(book, done);
    complete(book);
    return;
  }
  const source = new Map<string, Bend.TLD>();
  const holes = new Set<string>();
  const automaticDefs = new Set<string>();
  let serial = 0;
  let automatic = false;
  for (const [name, tld] of Object.entries(book.tlds)) {
    let copy = { ...tld };
    if (copy.$ === "Def" && !copy.b && !copy.i) {
      if (copy.v === null) automatic = true;
      else {
        const before = serial;
        const v = syntax(Bend.term_lower(copy.v), (t) => {
          if (t.$ !== "Hol" || t.k !== "auto") return t;
          // Each elaborated occurrence gets an identity, even when pattern
          // compilation duplicates one source span into several branches.
          const k = "\0why3/auto/" + serial++;
          holes.add(k);
          automatic = true;
          return { ...t, k };
        });
        // Preserve the kernel's source sharing in bodies with no auto holes.
        if (serial !== before) {
          copy = { ...copy, v: Bend.term_higher(v) };
          automaticDefs.add(name);
        }
      }
    }
    source.set(name, copy);
  }
  if (!automatic) {
    book.open = 0;
    Bend.book_valid(book, done);
    complete(book);
    return;
  }
  const last = new Map(book.order.map((k, i) => [k, i]));
  const context = new ProofContext();
  const lines = new SourceLines();
  const declarations = context.declarations;
  const previous = new Map<string, Declaration>();
  const pool = new ProofPool(options.jobs);
  const provers = new Set(options.provers?.length ? options.provers : ["alt-ergo"]);
  const width = 128 * Math.ceil(pool.limit / provers.size);
  const active = new Set<Promise<void>>();
  const stop = new AbortController();
  let failure: unknown;
  let task = 0;
  let temp: string | undefined;
  const batcher = new ProofBatcher(options, pool, stop.signal);
  const require_valid = (result: Result): void => {
    if (result.valid) return;
    const g = result.goal;
    throw new Error("Why3: " + (g.file ?? g.name) + (g.line === undefined ? "" : ":" + g.line)
      + ": could not prove " + g.name + " (" + result.attempts.map((a) => a.prover + ": "
        + a.answer.replace(/\s+/g, " ")).join(", ")
      + "). Supply a Bend proof, or increase --timeout.");
  };
  const elaborate = async (decl: Declaration, i: number) => {
    const name = decl.name;
    let tld = { ...decl.raw };
    const locals = new Map<string, Bend.Def>(), records = new Map<string, Evidence>();
    const facts: string[] = [];
    const discharge = async (goal: string, def: Bend.Def, display?: Goal): Promise<Evidence> => {
      const view = context.view(i, locals);
      const neededSymbols = context.needed(view.book, def.T);
      const pending = context.waiting(neededSymbols, i);
      if (pending.length) {
        const tr = new Translator(view.book, {}, view.trusted, lines);
        const needed = pending.filter((d) => {
          if (![...references(d.raw.T)].some((k) => view.book.tlds[k]?.$ === "Def")) return false;
          try { return tr.is_proposition(tr.normal(d.raw.T, true)); }
          catch (e) { if (!(e instanceof Unsupported)) throw e; return false; }
        });
        // Computational lemmas in the goal's theory are likely prerequisites.
        // Let them finish first; unrelated goals and simple identities overlap.
        await Promise.all(needed.map((d) => d.work));
      }
      temp ??= fs.mkdtempSync(path.join(os.tmpdir(), "bend-proof-"));
      const file = path.join(temp, "obligation-" + task++ + ".mlw");
      let selected: string[] = [];
      const attempt = async (all: boolean) => {
        context.validate(goal, def, i, locals);
        const current = new Map(locals);
        current.set(goal, def);
        const { book: prefix, trusted } = context.view(i, current);
        const tr = new Translator(prefix, { files: options.files, laws: [goal], induct: options.induct }, trusted, lines);
        if (display) tr.origins.set(goal, display);
        const needed = context.needed(prefix, def.T);
        selected = all ? context.available(i) : context.relevant(needed, i);
        selected.push(...(all ? [...locals.keys()] : tr.relevant([goal], [...locals.keys()])));
        const exported = tr.run(true, selected);
        if (display) exported.goals[0] = { ...display, id: exported.goals[0].id };
        fs.writeFileSync(file, exported.source);
        const result = await batcher.prove(file, exported.goals[0]);
        return { ...result, assumptions: exported.assumptions, source: exported.source,
          digest: crypto.createHash("sha256").update(exported.source).digest("hex") };
      };
      let result = await attempt(false);
      if (!result.valid) {
        // An independent attempt may run before useful earlier lemmas finish.
        // Retry only with verified predecessors; never assume pending goals.
        await Promise.all(declarations.slice(0, i).map((d) => d.work));
        const available = [...context.available(i), ...locals.keys()];
        if (available.some((f) => !selected.includes(f))) result = await attempt(true);
      }
      return result;
    };
    let validated: { book: Bend.Book; trusted: Trust };
    for (;;) {
      const current = new Map(locals);
      if (tld.$ === "Def") current.set(name, tld);
      const view = context.view(i, current);
      const { book: prefix, trusted } = view;
      try {
        context.validate(name, tld, i, locals, i < done);
        validated = view;
        break;
      } catch (error) {
        const err = error as Bend.Err;
        if (err?.$ !== "Err" || typeof err.obs !== "object" || err.obs?.$ !== "Hol"
          || !holes.has(err.obs.k) || typeof err.exp !== "object" || tld.$ !== "Def" || tld.v === null) throw error;
        const hole = err.obs.k;
        const display = new Translator(prefix, { files: options.files }, trusted, lines).location(name, err.spn);
        display.name += " (?auto)";
        let closed = close_goal(err, trusted, false, prefix, lines);
        const full = close_goal(err, trusted, true, prefix, lines);
        if (full.args.length !== closed.args.length
          && new Translator(prefix, {}, trusted, lines).needs_hypothesis(closed.type)) closed = full;
        const attempt = () => discharge(hole, { $: "Def", n: closed.args.length, T: closed.type, v: null }, display);
        let result = await attempt();
        if (!result.valid && full.args.length !== closed.args.length) {
          closed = full;
          result = await attempt();
        }
        require_valid(result);
        records.set(hole, result);
        locals.set(hole, { $: "Def", n: closed.args.length, T: closed.type, v: null, b: true });
        facts.push(hole);
        const replacement = Bend.term_lower(apply(Bend.Ref(hole), closed.args));
        tld.v = Bend.term_higher(syntax(Bend.term_lower(tld.v), (t) =>
          t.$ === "Hol" && t.k === hole ? replacement : t));
        // Retry the entire definition: the kernel checks quantities,
        // recursion, and all uses of the freshly proved theorem normally.
      }
    }
    if (tld.$ === "Def" && last.get(name) === i && !tld.b && !tld.i) {
      if (tld.v === null) {
        const result = await discharge(name, tld);
        require_valid(result);
        records.set(name, result);
        facts.push(name);
        // Native flags are installed only after a validated ATP answer.
        tld = { ...tld, v: null, e: undefined, b: true };
      } else {
        const { book: prefix, trusted } = validated;
        const tr = new Translator(prefix, {}, trusted, lines);
        try {
          if (tr.is_proposition(tr.normal(tld.T, true))) facts.push(name);
        } catch (e) {
          if (!(e instanceof Unsupported)) throw e;
        }
      }
    }
    decl.result = { tld, locals, facts, records };
    context.accept(decl);
  };
  try {
    // Check the ordinary prefix in one kernel pass. It has no automatic
    // obligations, so constructing a worker and prefix per definition would
    // only add work to the program's native checking cost.
    let first = 0;
    for (; first < book.order.length; first++) {
      const name = book.order[first], raw = source.get(name)!;
      const fin = last.get(name) === first;
      if (fin && raw.$ === "Def" && !raw.b && !raw.i && (raw.v === null || automaticDefs.has(name))) break;
      const tld = raw.$ === "Def" && !fin ? { ...raw, v: null, e: undefined } : raw;
      const decl: Declaration = { name, raw: tld, at: first, work: Promise.resolve() };
      context.add(decl, false);
      previous.set(name, decl);
    }
    const initial = context.assemble();
    Bend.book_valid(initial, done);
    for (const [i, decl] of declarations.entries()) {
      const tld = decl.raw, facts: string[] = [];
      if (last.get(decl.name) === i && tld.$ === "Def" && !tld.b && !tld.i && tld.v !== null) {
        const tr = new Translator(initial, {}, new Set(), lines);
        try { if (tr.is_proposition(tr.normal(tld.T, true))) facts.push(decl.name); }
        catch (e) { if (!(e instanceof Unsupported)) throw e; }
      }
      decl.result = { tld, facts, locals: new Map(), records: new Map() };
      context.accept(decl);
    }
    for (let i = first; i < book.order.length; i++) {
      if (stop.signal.aborted) throw failure;
      const name = book.order[i], raw = source.get(name)!;
      const fin = last.get(name) === i;
      const tld = raw.$ === "Def" && !fin ? { ...raw, v: null, e: undefined } : raw;
      const concurrent = fin && tld.$ === "Def" && !tld.b && !tld.i && (tld.v === null || automaticDefs.has(name));
      // Prepare a bounded window, so queued goals do not capture stale fact
      // sets long before a process slot becomes available. One job is serial.
      if (concurrent) while (active.size >= width) await Promise.race(active);
      if (active.size) {
        const refs = new Set(references(tld.T));
        const terms = tld.$ === "ADT" ? tld.c.map((c) => c.T) : tld.v === null ? [] : [tld.v];
        for (const term of terms) for (const ref of references(term)) refs.add(ref);
        const dependencies = [...refs].map((ref) => previous.get(ref)).filter((d) => d && !d.result);
        if (dependencies.length) await Promise.all(dependencies.map((d) => d!.work));
      }
      const decl: Declaration = { name, raw: tld, at: i, work: Promise.resolve() };
      context.add(decl, concurrent);
      previous.set(name, decl);
      decl.work = elaborate(decl, i).catch((e) => {
        failure ??= e;
        stop.abort();
        throw e;
      });
      // Attach a handler immediately even when an independent worker fails
      // before the main loop reaches its final join.
      void decl.work.catch(() => {});
      if (concurrent) {
        active.add(decl.work);
        void decl.work.then(() => active.delete(decl.work), () => active.delete(decl.work));
      } else await decl.work;
    }
    await Promise.all(declarations.map((d) => d.work));
    const checked = context.assemble();
    const records = new Map(declarations.flatMap((d) => [...d.result!.records]));
    // Commit only a fully checked book. A failed goal never leaks an admitted
    // definition into a caller that catches the error and reuses its input.
    book.tlds = checked.tlds;
    book.ctrs = checked.ctrs;
    book.order = checked.order;
    book.open = 0;
    certified.set(book, records);
  } catch (e) {
    throw failure ?? e;
  } finally {
    stop.abort();
    await Promise.allSettled(declarations.map((d) => d.work));
    if (temp !== undefined) fs.rmSync(temp, { recursive: true, force: true });
  }
}

// Runtime erasure is deliberately separate from the checking book. Equality
// evidence has no data, so its runtime token is reflexivity; it is NEVER fed
// back into the kernel as a proof. Existentials and sums stay opaque, since an
// ATP's validity answer cannot supply their witnesses or constructor choices.
export function runtime_book(book: Bend.Book): Bend.Book {
  const records = certified.get(book);
  if (!records?.size) return book;
  const tr = new Translator(book, {}, new Set(records.keys()));
  const erase = (type: Term, depth = 0): Term | null => {
    const t = tr.normal(type, true);
    if (t.$ === "Eql") return Bend.Rfl();
    if (t.$ === "All") {
      const body = erase(t.B(Bend.Var(t.k, depth)), depth + 1);
      return body === null ? null : Bend.term_higher(Bend.Lam(t.k, depth, Bend.term_lower(body, depth + 1), t.s, t.q));
    }
    if (tr.base && t.$ === "ADT" && t.k === "Unit") return Bend.Ctr("Unit", []);
    if (tr.base && t.$ === "ADT" && t.k === "Sigma") {
      const a = erase(t.x[2], depth);
      const b = a === null ? null : erase(apply(t.x[3], [a]), depth);
      return a === null || b === null ? null : Bend.Ctr("Tuple", [a, b]);
    }
    return null;
  };
  const out = { ...book, tlds: { ...book.tlds } };
  for (const [name, tld] of Object.entries(book.tlds)) {
    if (tld.$ !== "Def") continue;
    if (records.has(name)) {
      const v = erase(tld.T);
      out.tlds[name] = { ...tld, v, e: v === null ? undefined : Bend.term_lower(v) };
    } else if (tld.v !== null) {
      // Match the compiler's existing operational erasure of equality
      // elimination, including proofs that destruct opaque existential facts.
      const strip = (t: Bend.LTerm): Bend.LTerm => t.$ === "Rwt" ? strip(t.f) : t;
      out.tlds[name] = { ...tld, v: Bend.term_higher(syntax(Bend.term_lower(tld.v), strip)),
        e: tld.e === undefined ? undefined : syntax(tld.e, strip) };
    }
  }
  certified.set(out, records);
  return out;
}

export function executable_value(book: Bend.Book, term: Term): void {
  const records = certified.get(book);
  if (!records?.size) return;
  syntax(Bend.term_lower(term), (t) => {
    if (t.$ === "Ref" && records.has(t.k) && (book.tlds[t.k] as Bend.Def).v === null) {
      throw new Error("Why3: cannot execute opaque theorem " + records.get(t.k)!.goal.name
        + "; supply a Bend body to compute its witness or constructor choice");
    }
    return t;
  });
}

// why3 --json is a stream of pretty-printed objects, not one JSON array and
// not JSONL. Reject malformed, missing, or unexpected answers, even on exit 0.
export function read_answers(output: string): { name: string; answer: string; time: number }[] {
  const values: { name: string; answer: string; time: number }[] = [];
  let start = -1, depth = 0, quoted = false, escaped = false;
  for (let i = 0; i < output.length; i++) {
    const c = output[i];
    if (start < 0) {
      if (/\s/.test(c)) continue;
      if (c !== "{") throw new Error("Why3: unexpected non-JSON prover output");
      start = i;
    }
    if (quoted) {
      if (escaped) escaped = false;
      else if (c === "\\") escaped = true;
      else if (c === '"') quoted = false;
    } else if (c === '"') quoted = true;
    else if (c === "{") depth++;
    else if (c === "}" && --depth === 0) {
      const v = JSON.parse(output.slice(start, i + 1));
      if (typeof v.term?.goal_name !== "string" || typeof v["prover-result"]?.answer !== "string"
        || typeof v["prover-result"]?.time !== "number" || !Number.isFinite(v["prover-result"].time)
        || v["prover-result"].time < 0) {
        throw new Error("Why3: malformed prover result");
      }
      values.push({ name: v.term.goal_name, answer: v["prover-result"].answer, time: v["prover-result"].time });
      start = -1;
    }
  }
  if (start >= 0) throw new Error("Why3: truncated prover output");
  return values;
}

// One shared limit covers both independent goals and each prover portfolio.
// Queued attempts can be cancelled without starting another process.
class ProofPool {
  active = 0;
  waiting: (() => void)[] = [];
  limit: number;
  constructor(jobs = Math.min(16, os.availableParallelism())) {
    if (!Number.isInteger(jobs) || jobs < 1 || jobs > 64) {
      throw new Error("Why3: jobs must be an integer from 1 to 64");
    }
    this.limit = jobs;
  }
  async run<T>(action: () => Promise<T>, signal: AbortSignal): Promise<T> {
    const cancelled = () => new Error("Why3: prover attempt cancelled");
    await new Promise<void>((resolve, reject) => {
      if (signal.aborted) { reject(cancelled()); return; }
      const start = () => {
        signal.removeEventListener("abort", abort);
        this.active++;
        resolve();
      };
      const abort = () => {
        this.waiting = this.waiting.filter((f) => f !== start);
        reject(cancelled());
      };
      if (this.active < this.limit) start();
      else { this.waiting.push(start); signal.addEventListener("abort", abort, { once: true }); }
    });
    try {
      if (signal.aborted) throw cancelled();
      return await action();
    } finally {
      this.active--;
      this.waiting.shift()?.();
    }
  }
}

type ProofTask = { file: string; goal: Goal };
type QueuedProof = ProofTask & { resolve: (result: Result) => void; reject: (error: unknown) => void };

// Coalesce ready, independent tasks. A worker is one Why3 process reused for
// up to 32 goals, each in its own input theory. Why3 runs its ATP sequentially,
// so a pool slot still represents at most one live solver. Dependent tasks
// cannot enter a batch until their premises have been verified.
class ProofBatcher {
  queued: QueuedProof[] = [];
  scheduled = false;
  active = 0;
  partial: ReturnType<typeof setTimeout> | undefined;
  readonly options: ProveOptions;
  readonly pool: ProofPool;
  readonly signal: AbortSignal;
  constructor(options: ProveOptions, pool: ProofPool, signal: AbortSignal) {
    this.options = options;
    this.pool = pool;
    this.signal = signal;
  }
  prove(file: string, goal: Goal): Promise<Result> {
    const promise = new Promise<Result>((resolve, reject) => this.queued.push({ file, goal, resolve, reject }));
    this.schedule();
    return promise;
  }
  schedule(): void {
    if (!this.scheduled) {
      this.scheduled = true;
      setTimeout(() => this.flush(), 0);
    }
  }
  flush(partial = false): void {
    this.scheduled = false;
    const provers = new Set(this.options.provers?.length ? this.options.provers : ["alt-ergo"]).size;
    const workers = Math.max(1, Math.ceil(this.pool.limit / provers));
    // Keep requests together while workers are occupied. Queuing tiny batches
    // inside ProofPool freezes their size before more ready goals can join.
    while (this.queued.length && this.active < workers) {
      if (!partial && this.active && this.queued.length < 32) {
        this.partial ??= setTimeout(() => { this.partial = undefined; this.flush(true); }, 20);
        break;
      }
      const size = this.queued.length >= 32 ? 32 : this.active ? this.queued.length
        : Math.ceil(this.queued.length / workers);
      const batch = this.queued.splice(0, size);
      this.active++;
      void prove_batch(batch, this.options, this.pool, this.signal).then(
        (results) => results.forEach((result, j) => batch[j].resolve(result)),
        (error) => batch.forEach((item) => item.reject(error))).finally(() => {
          this.active--;
          this.schedule();
        });
    }
    if (!this.queued.length && this.partial !== undefined) { clearTimeout(this.partial); this.partial = undefined; }
  }
}

async function prove_batch(tasks: ProofTask[], options: ProveOptions, pool: ProofPool, signal: AbortSignal): Promise<Result[]> {
  if (new Set(tasks.map((t) => t.goal.id)).size !== tasks.length) throw new Error("Why3: duplicate proof obligation");
  const provers = [...new Set(options.provers?.length ? options.provers : ["alt-ergo"])];
  const controllers = provers.map(() => new AbortController());
  const results = tasks.map(({ goal }): Result => ({ goal, valid: false, attempts: [] }));
  const by_id = new Map(results.map((r) => [r.goal.id, r]));
  const jobs: Promise<void>[] = [];
  let pending = provers.length, finished = false;
  const result = new Promise<Result[]>((resolve, reject) => {
    provers.forEach((prover, i) => {
      const attemptSignal = AbortSignal.any([signal, controllers[i].signal]);
      jobs.push(pool.run(async () => {
        const remaining = tasks.filter((t) => !by_id.get(t.goal.id)!.valid);
        return remaining.length ? invoke_tasks(remaining, { ...options, provers: [prover] }, attemptSignal) : [];
      }, attemptSignal).then((answers) => {
        if (finished) return;
        for (const answer of answers) {
          const r = by_id.get(answer.goal.id)!;
          if (r.valid) continue;
          r.attempts.push(...answer.attempts);
          r.valid = answer.valid;
        }
        if (results.every((r) => r.valid) || --pending === 0) {
          finished = true;
          resolve(results);
        }
      }).catch((error) => {
        if (!finished) { finished = true; reject(error); }
      }));
    });
  });
  try { return await result; }
  finally {
    controllers.forEach((c) => c.abort());
    await Promise.allSettled(jobs);
  }
}

export async function prove(file: string, goals: Goal[], options: ProveOptions = {}, signal?: AbortSignal): Promise<Result[]> {
  if (goals.length === 0) throw new Error("Why3: no proof obligations");
  if (new Set(goals.map((g) => g.id)).size !== goals.length) throw new Error("Why3: duplicate proof obligation");
  const pool = new ProofPool(options.jobs);
  const stop = new AbortController();
  const combined = signal ? AbortSignal.any([signal, stop.signal]) : stop.signal;
  const batcher = new ProofBatcher(options, pool, combined);
  const jobs = goals.map((goal) => batcher.prove(file, goal));
  try {
    return await Promise.all(jobs);
  } finally {
    stop.abort();
    await Promise.allSettled(jobs);
  }
}

async function invoke_tasks(tasks: ProofTask[], options: ProveOptions, signal: AbortSignal): Promise<Result[]> {
  const timeout = options.timeout ?? 5;
  if (!Number.isInteger(timeout) || timeout < 1 || timeout > 3600) {
    throw new Error("Why3: timeout must be an integer from 1 to 3600 seconds");
  }
  if (tasks.length === 0) throw new Error("Why3: no proof obligations");
  const results = tasks.map(({ goal }): Result => ({ goal, valid: false, attempts: [] }));
  for (const prover of new Set(options.provers?.length ? options.provers : ["alt-ergo"])) {
    const pending = results.filter((r) => !r.valid);
    if (pending.length === 0) break;
    const files = new Map<string, string[]>();
    for (const task of tasks) if (!results.find((r) => r.goal.id === task.goal.id)!.valid) {
      const ids = files.get(task.file) ?? [];
      ids.push(task.goal.id);
      files.set(task.file, ids);
    }
    const args = ["prove", "--json", "-P", prover, "-t", String(timeout),
      // Induction yields one obligation per law. Splitting can erase true goals
      // without a JSON answer, making complete result accounting impossible.
      "-a", "induction_ty_lex", ...(options.config ? ["-C", options.config] : []),
      ...[...files].flatMap(([file, ids]) => [file, "-T", "Bend", ...ids.flatMap((id) => ["-G", id])])];
    const run = await new Promise<{ stdout: string; stderr: string; code: number | null }>((resolve, reject) => {
      const processGroup = process.platform !== "win32";
      const proc = child.spawn(options.binary ?? "why3", args,
        { detached: processGroup, stdio: ["ignore", "pipe", "pipe"] });
      let stdout = "", stderr = "", bytes = 0;
      let failure: Error | undefined;
      const stop = (error: Error) => {
        failure ??= error;
        try {
          if (processGroup && proc.pid !== undefined) process.kill(-proc.pid, "SIGKILL");
          else proc.kill("SIGKILL");
        } catch { proc.kill("SIGKILL"); }
      };
      const abort = () => stop(new Error("Why3: prover attempt cancelled"));
      const timer = setTimeout(() => stop(new Error("Why3: prover process timed out")),
        (timeout * pending.length + 15) * 1000);
      const collect = (text: string, output: boolean) => {
        bytes += Buffer.byteLength(text);
        if (bytes > 16 * 1024 * 1024) { stop(new Error("Why3: prover output limit exceeded")); return; }
        if (output) stdout += text; else stderr += text;
      };
      proc.stdout.setEncoding("utf8").on("data", (s: string) => collect(s, true));
      proc.stderr.setEncoding("utf8").on("data", (s: string) => collect(s, false));
      proc.once("error", (error: NodeJS.ErrnoException) => {
        const hint = error.code === "ENOENT" ? "\nInstall Why3 and a prover, then run 'why3 config detect'." : "";
        failure = new Error("Why3: invocation failed: " + error.message + hint);
      });
      proc.once("close", (code) => {
        clearTimeout(timer);
        signal?.removeEventListener("abort", abort);
        if (failure) reject(failure); else resolve({ stdout, stderr, code });
      });
      signal?.addEventListener("abort", abort, { once: true });
      if (signal?.aborted) abort();
    });
    if (run.code !== 0 && run.code !== 2) throw new Error("Why3: prover invocation failed\n" + run.stderr.trim());
    const answers = read_answers(run.stdout);
    const by_id = new Map(pending.map((r) => [r.goal.id, r]));
    for (const a of answers) {
      const r = by_id.get(a.name);
      if (!r || r.attempts.some((a) => a.prover === prover)) throw new Error("Why3: duplicate or unexpected goal " + a.name);
      r.attempts.push({ prover, answer: a.answer, time: a.time });
      r.valid = a.answer === "Valid";
    }
    if (answers.length !== pending.length) {
      throw new Error("Why3: incomplete results (" + answers.length + "/" + pending.length + ")\n" + run.stderr.trim());
    }
    if (run.code !== 0 && pending.every((r) => r.valid)) {
      throw new Error("Why3: unsuccessful exit despite Valid answers\n" + run.stderr.trim());
    }
  }
  return results;
}
