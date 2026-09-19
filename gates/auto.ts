#!/usr/bin/env bun
// Integrated proof-system gate. The small fake prover tests the trust boundary;
// real Why3 checks exercise theorem reuse, local goals, imports and execution.
import * as assert from "node:assert/strict";
import * as child from "node:child_process";
import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import * as Bend from "../bend2/bend.ts";
import * as Why3 from "../bend2/why3.ts";

const ROOT = path.resolve(import.meta.dirname, "..");
const TEMP = fs.mkdtempSync(path.join(os.tmpdir(), "bend-auto-test-"));
const CLI = path.join(ROOT, "bend2/main.ts");
const WHY3 = process.env.WHY3 ?? "why3";
const PROVER = process.env.WHY3_PROVER ?? "alt-ergo";
const options = { binary: WHY3, provers: [PROVER], timeout: 1 };
const env = { ...process.env, BEND_NO_TELEMETRY: "1", BEND_WHY3: WHY3, BEND_WHY3_PROVERS: PROVER, BEND_WHY3_TIMEOUT: "1" };
const BUN = process.versions.bun ? process.execPath : process.env.BUN ?? "bun";
const NODE = process.versions.bun ? [] : ["--disable-warning=MODULE_TYPELESS_PACKAGE_JSON"];
let checks = 0;
function check(f: () => void): void { f(); checks++; }
async function rejects(f: () => Promise<unknown>, pattern: RegExp): Promise<void> {
  await assert.rejects(f, pattern); checks++;
}
function run(args: string[], overrides = env) {
  return child.spawnSync(BUN, [CLI, ...args],
    { cwd: ROOT, env: overrides, encoding: "utf8", timeout: 60000 });
}
async function read(file: string) {
  const book = Bend.book_nil();
  const files = new Map<string, string | null>();
  await Bend.book_load(book, file, "", files);
  return { book, files };
}
function file(name: string, source: string): string {
  const out = path.join(TEMP, name + ".bend");
  fs.writeFileSync(out, "import Base\n" + source + "\n");
  return out;
}

async function orchestration(): Promise<void> {
  const binary = path.join(TEMP, "prover stub");
  const log = path.join(TEMP, "tasks.jsonl");
  const stub = (fail = false) => fs.writeFileSync(binary, `#!/usr/bin/env node
const fs = require('node:fs');
const args = process.argv.slice(2);
const input = args.find(x => x.endsWith('.mlw'));
const source = fs.readFileSync(input, 'utf8');
fs.appendFileSync(${JSON.stringify(log)}, JSON.stringify({args, source})+'\\n');
const ids = args.flatMap((x,i) => x === '-G' ? [args[i+1]] : []);
const answer = ${fail} && source.includes('goal Law_second:') ? 'Unknown' : 'Valid';
for (const id of ids) console.log(JSON.stringify({term:{goal_name:id},'prover-result':{answer,time:0}}));
process.exitCode = answer === 'Valid' ? 0 : 2;
`, { mode: 0o755 });
  const src = file("order", `
law first:
  for n: Nat
  {Nat.add(n, 0n) == n : Nat}
def manual(n: Nat) -> {Nat.add(n, 0n) == n : Nat}: first(n)
law second:
  for n: Nat
  {Nat.add(Nat.add(n, 0n), 0n) == n : Nat}
def future(n: Nat) -> {n == n : Nat}: {==}
`);
  stub();
  const { book, files } = await read(src);
  await Why3.check_book(book, { binary, files });
  const reports = Why3.evidence(book);
  const tasks = fs.readFileSync(log, "utf8").trim().split("\n").map((l) => JSON.parse(l));
  check(() => assert.equal(reports.length, 2));
  check(() => assert.deepEqual(reports[0].assumptions, []));
  check(() => assert.deepEqual(reports[1].assumptions, ["first", "manual"]));
  check(() => assert.match(reports[0].digest, /^[a-f0-9]{64}$/));
  check(() => assert.ok(tasks.every((t) => t.args[t.args.indexOf("-t") + 1] === "1")));
  check(() => assert.ok(!tasks[0].source.includes("axiom")));
  check(() => assert.ok(tasks[1].source.includes("axiom Fact_first:")));
  check(() => assert.ok(!tasks.some((t) => t.source.includes("axiom Fact_future:"))));
  check(() => assert.ok(!tasks[1].source.includes("axiom Fact_second:")));
  check(() => assert.equal((book.tlds.first as Bend.Def).v, null));
  check(() => assert.equal((book.tlds.first as Bend.Def).b, true));
  check(() => Bend.book_valid(book)); // The completed manual proofs check against opaque facts.
  const runtime = Why3.runtime_book(book);
  check(() => assert.notEqual((runtime.tlds.first as Bend.Def).v, null));
  check(() => assert.equal((book.tlds.first as Bend.Def).v, null));
  await rejects(() => Why3.check_book(book), /reload the source/);

  stub(true);
  const bad = await read(src);
  await rejects(() => Why3.check_book(bad.book, { binary, files: bad.files }), /could not prove second/);
  check(() => assert.equal((bad.book.tlds.first as Bend.Def).b, undefined));
  check(() => assert.equal((bad.book.tlds.first as Bend.Def).v, null));
  check(() => assert.equal(Why3.evidence(bad.book).length, 0));

  stub();
  const unsafe = file("unsafe_fact", `
@unsafe
def false_fact() -> {0n == 1n : Nat}: false_fact()
law safe: {0n == 0n : Nat}
`);
  const u = await read(unsafe);
  await Why3.check_book(u.book, { binary });
  check(() => assert.deepEqual(Why3.evidence(u.book)[0].assumptions, []));
  const invalid = file("invalid_body", "def wrong() -> {0n == 1n : Nat}: {==}");
  const before = fs.readFileSync(log, "utf8");
  const v = await read(invalid);
  await assert.rejects(() => Why3.check_book(v.book, { binary })); checks++;
  check(() => assert.equal(fs.readFileSync(log, "utf8"), before));
  const todo = file("todo", "def unfinished() -> {0n == 1n : Nat}: ?TODO\nlaw goal: {0n == 0n : Nat}");
  const t = await read(todo);
  await rejects(() => Why3.check_book(t.book, { binary }), /TODOs? found/);
  check(() => assert.equal(Why3.evidence(t.book).length, 0));
  check(() => assert.equal(fs.readFileSync(log, "utf8"), before));
  check(() => assert.equal(run([todo, "--why3-bin", binary]).status, 1));
  const kernel = run([src, "--kernel-only", "--why3-bin", path.join(TEMP, "absent")]);
  check(() => assert.equal(kernel.status, 1));
  check(() => assert.ok(!kernel.stderr.includes("invocation failed")));
  const manual = file("manual", "def reflexive(n: Nat) -> {n == n : Nat}: {==}");
  check(() => assert.equal(run([manual, "--why3-bin", path.join(TEMP, "absent")]).status, 0));
  const implicit = run([src, "--why3-bin", binary]);
  check(() => assert.equal(implicit.status, 0, implicit.stderr));
  check(() => assert.match(implicit.stdout, /Why3 proved 2 obligations/));
}

async function strategies(): Promise<void> {
  const binary = path.join(TEMP, "strategy stub");
  const log = path.join(TEMP, "focused.jsonl");
  fs.writeFileSync(binary, `#!/usr/bin/env node
const fs = require('node:fs');
const args = process.argv.slice(2);
const source = fs.readFileSync(args.find(x => x.endsWith('.mlw')), 'utf8');
const id = args[args.indexOf('-G') + 1];
fs.appendFileSync(${JSON.stringify(log)}, JSON.stringify({id,source})+'\\n');
const valid = id !== 'Law_filtered' || source.includes('axiom Fact_bridge:');
console.log(JSON.stringify({term:{goal_name:id},'prover-result':{answer:valid?'Valid':'Unknown',time:0}}));
process.exitCode = valid ? 0 : 2;
`, { mode: 0o755 });
  const src = file("focused", `
def identity(n: Nat) -> Nat: n
law bridge:
  for n: Nat
  {identity(n) == n : Nat}
law filtered:
  for n: Nat
  {n == n : Nat}
`);
  const focused = await read(src);
  await Why3.check_book(focused.book, { binary });
  const tasks = fs.readFileSync(log, "utf8").trim().split("\n").map((s) => JSON.parse(s));
  check(() => assert.equal(tasks.length, 3));
  check(() => assert.ok(!tasks[1].source.includes("Fact_bridge")));
  check(() => assert.ok(tasks[2].source.includes("axiom Fact_bridge:")));
  check(() => assert.deepEqual(Why3.evidence(focused.book)[1].assumptions, ["bridge"]));

  // The second prover can finish while the first is still running. Its win
  // must stop both the losing Why3 process and its solver child on POSIX.
  const parent = path.join(TEMP, "loser.pid"), descendant = path.join(TEMP, "solver.pid");
  const sleeper = path.join(TEMP, "solver.cjs");
  fs.writeFileSync(sleeper, `require('node:fs').writeFileSync(${JSON.stringify(descendant)}, String(process.pid));
setInterval(() => {}, 1000);
`);
  fs.writeFileSync(binary, `#!/usr/bin/env node
const fs = require('node:fs');
const args = process.argv.slice(2);
if (args[args.indexOf('-P') + 1] === 'slow') {
  fs.writeFileSync(${JSON.stringify(parent)}, String(process.pid));
  if (process.platform !== 'win32') require('node:child_process').spawn(process.execPath, [${JSON.stringify(sleeper)}], {stdio:'inherit'});
  else fs.writeFileSync(${JSON.stringify(descendant)}, String(process.pid));
  setInterval(() => {}, 1000);
} else {
  const deadline = Date.now() + 5000;
  const poll = setInterval(() => {
    if (fs.existsSync(${JSON.stringify(descendant)})) {
      clearInterval(poll);
      console.log(JSON.stringify({term:{goal_name:args[args.indexOf('-G')+1]},'prover-result':{answer:'Valid',time:0}}));
    } else if (Date.now() > deadline) process.exit(1);
  }, 10);
}
`, { mode: 0o755 });
  const race = await read(file("race", "law goal: {0n == 0n : Nat}"));
  await Why3.check_book(race.book, { binary, provers: ["slow", "fast"], timeout: 1 });
  check(() => assert.deepEqual(Why3.evidence(race.book)[0].attempts.map((a) => a.prover), ["fast"]));
  const running = (pid: number): boolean => {
    try {
      process.kill(pid, 0);
      // A killed grandchild may briefly await its new parent's waitpid.
      if (process.platform === "linux" && /\) Z /.test(fs.readFileSync("/proc/" + pid + "/stat", "utf8"))) return false;
      return true;
    } catch (e) {
      if (["ESRCH", "ENOENT"].includes((e as NodeJS.ErrnoException).code ?? "")) return false;
      throw e;
    }
  };
  for (const pidFile of [parent, descendant]) {
    check(() => assert.equal(running(Number(fs.readFileSync(pidFile, "utf8"))), false, pidFile));
  }
}

async function parallel_goals(): Promise<void> {
  const binary = path.join(TEMP, "parallel stub"), log = path.join(TEMP, "parallel.jsonl");
  const ready = path.join(TEMP, "fast-ready");
  const stub = (fail = false) => fs.writeFileSync(binary, `#!/usr/bin/env node
const fs = require('node:fs');
const args = process.argv.slice(2), id = args[args.indexOf('-G')+1];
const input = args.find(x => x.endsWith('.mlw')), source = fs.readFileSync(input, 'utf8');
fs.appendFileSync(${JSON.stringify(log)}, JSON.stringify({id,input,source})+'\\n');
if (!source.includes('goal '+id+':')) process.exit(1);
const answer = () => {
  const valid = !${fail} || id !== 'Law_slow';
  console.log(JSON.stringify({term:{goal_name:id},'prover-result':{answer:valid?'Valid':'Unknown',time:0}}));
  process.exitCode = valid ? 0 : 2;
};
if (id === 'Law_slow') {
  const deadline = Date.now()+5000;
  const poll = setInterval(() => {
    if (fs.existsSync(${JSON.stringify(ready)})) { clearInterval(poll); setTimeout(answer, 80); }
    else if (Date.now()>deadline) process.exit(1);
  }, 10);
} else { fs.writeFileSync(${JSON.stringify(ready)}, 'ready'); answer(); }
`, { mode: 0o755 });
  stub();
  const src = file("parallel", `
law slow: {0n == 0n : Nat}
def fast(n: Nat) -> {n == n : Nat}: ?auto
def dependent() -> {0n == 0n : Nat}: slow
law after: {2n == 2n : Nat}
`);
  const loaded = await read(src);
  await Why3.check_book(loaded.book, { binary, provers: ["stub"], jobs: 2 });
  const tasks = fs.readFileSync(log, "utf8").trim().split("\n").map((s) => JSON.parse(s));
  check(() => assert.equal(tasks.length, 3));
  check(() => assert.equal(new Set(tasks.map((t) => t.input)).size, 3));
  check(() => assert.ok(tasks.filter((t) => t.id !== "Law_after").every((t) => !t.source.includes("axiom"))));
  const after = tasks.find((t) => t.id === "Law_after");
  check(() => assert.match(after.source, /axiom Fact_slow:/));
  check(() => assert.match(after.source, /axiom Fact_dependent:/));
  check(() => assert.deepEqual(Why3.evidence(loaded.book).map((e) => e.goal.name), ["slow", "fast (?auto)", "after"]));
  check(() => Bend.book_valid(loaded.book));

  stub(true);
  fs.rmSync(ready);
  const failed = await read(src);
  await rejects(() => Why3.check_book(failed.book, { binary, provers: ["stub"], jobs: 2 }), /could not prove slow/);
  check(() => assert.equal(Why3.evidence(failed.book).length, 0));
  check(() => assert.equal((failed.book.tlds.slow as Bend.Def).b, undefined));
  check(() => assert.match(Bend.term_show(Bend.term_lower((failed.book.tlds.fast as Bend.Def).v!)), /\?auto/));
}

async function batches(): Promise<void> {
  const binary = path.join(TEMP, "batch stub"), log = path.join(TEMP, "batches.jsonl");
  fs.writeFileSync(binary, `#!/usr/bin/env node
const fs = require('node:fs'), args = process.argv.slice(2);
const mode = args[args.indexOf('-P')+1], tasks = [];
let file;
for (let i=0;i<args.length;i++) {
  if (args[i].endsWith('.mlw')) file = args[i];
  if (args[i]==='-G') {
    const id = args[++i], source = fs.readFileSync(file,'utf8');
    if (!source.includes('goal '+id+':')) process.exit(1);
    tasks.push({file,id,source});
  }
}
fs.appendFileSync(${JSON.stringify(log)},JSON.stringify(tasks)+'\\n');
const emit = id => console.log(JSON.stringify({term:{goal_name:id},'prover-result':{answer:'Valid',time:0}}));
tasks.forEach((t,i) => { if (mode!=='missing' || i!==tasks.length-1) emit(t.id); });
if (mode==='duplicate') emit(tasks[0].id);
if (mode==='unexpected') emit('Law_unrequested');
if (mode==='trailing') process.stdout.write('{');
if (mode==='exit') process.exitCode=1;
`, { mode: 0o755 });
  const src = file("batch", Array.from({ length: 64 }, (_, i) =>
    "law g" + i + ": for n: Nat {n == n : Nat}").join("\n") + `
def reuse(n: Nat) -> {n == n : Nat}: g0(n)
law last: for n: Nat {Nat.add(n, 0n) == n : Nat}
def future(n: Nat) -> {n == n : Nat}: {==}
`);
  const loaded = await read(src);
  await Why3.check_book(loaded.book, { binary, provers: ["valid"], jobs: 2 });
  const calls: { file: string; id: string; source: string }[][] = fs.readFileSync(log, "utf8").trim().split("\n").map((s) => JSON.parse(s));
  const tasks = calls.flat();
  check(() => assert.ok(calls.length < 10, "reuse each Why3 process across multiple goals"));
  check(() => assert.ok(calls.some((c) => c.length > 1), "exercise a batch"));
  check(() => assert.equal(tasks.length, 65));
  check(() => assert.equal(new Set(tasks.map((t) => t.file)).size, 65, "isolate each goal's premises"));
  check(() => assert.ok(tasks.every((t) => !t.source.includes("Fact_future"))));
  check(() => assert.ok(tasks.filter((t) => /^Law_g\d+$/.test(t.id)).every((t) => {
    const i = Number(t.id.slice(5));
    return [...t.source.matchAll(/axiom Fact_g(\d+):/g)].every((m) => Number(m[1]) < i);
  }), "later batch results never become earlier premises"));
  check(() => assert.match(tasks.find((t) => t.id === "Law_last")!.source, /axiom Fact_reuse:/));
  check(() => assert.deepEqual(Why3.evidence(loaded.book).map((e) => e.goal.name),
    [...Array.from({ length: 64 }, (_, i) => "g" + i), "last"]));
  check(() => Bend.book_valid(loaded.book));

  for (const mode of ["missing", "duplicate", "unexpected", "trailing", "exit"]) {
    const bad = await read(src);
    await rejects(() => Why3.check_book(bad.book, { binary, provers: [mode], jobs: 2 }), /Why3:/);
    check(() => assert.equal(Why3.evidence(bad.book).length, 0));
    check(() => assert.ok(Array.from({ length: 64 }, (_, i) => bad.book.tlds["g" + i] as Bend.Def).every((d) => d.b === undefined)));
  }
  const forward = await read(file("forward", `
law value: Nat
law early: {value == 0n : Nat}
def value(): 0n
`));
  await rejects(() => Why3.check_book(forward.book, { binary, provers: ["valid"] }), /unfilled computational dependency value/);
  check(() => assert.equal(Why3.evidence(forward.book).length, 0));
}

async function actual_proofs(): Promise<void> {
  for (const name of fs.readdirSync(path.join(ROOT, "tests/auto")).sort()) {
    const src = path.join(ROOT, "tests/auto", name);
    const r = run([src]);
    const want = fs.readFileSync(src, "utf8").split("\n").filter((l) => l.startsWith("#|"))
      .map((l) => l.slice(2)).join("\n");
    check(() => assert.equal(r.status, 0, r.stderr));
    check(() => assert.equal(r.stdout.trim(), want, name));
  }
  // The closed local obligations retain live premises only when needed.
  const local = await read(path.join(ROOT, "tests/auto/local.bend"));
  await Why3.check_book(local.book, { ...options, files: local.files });
  const lemmas = Object.entries(local.book.tlds).filter(([k]) => k.startsWith("\0why3/"));
  check(() => assert.equal(lemmas.length, 7));
  check(() => assert.ok(lemmas.some(([, d]) => Bend.term_show(Bend.term_lower(d.T)).includes("h:"))));
  check(() => assert.equal(Why3.evidence(local.book).length, 7));

  for (const name of ["false", "erased", "unsafe", "ignored_unsafe", "unsafe_alias", "unfilled", "negative", "nonempty"]) {
    const src = path.join(ROOT, "tests/why3", name + ".bend");
    const r = run([src]);
    check(() => assert.equal(r.status, 1, name + ": " + r.stdout));
    check(() => assert.ok(!r.stdout.includes("All terms check."), name));
  }
  const erased = file("dead_premise", "def unsound(-h: {0n == 1n : Nat}) -> {0n == 1n : Nat}: ?auto");
  check(() => assert.equal(run([erased]).status, 1));
  const circular = file("circular", "def unsound() -> {0n == 1n : Nat}: ?auto");
  check(() => assert.equal(run([circular]).status, 1));
  const untyped = file("untyped", "def bad() -> Nat: ?auto(0n)");
  check(() => assert.equal(run([untyped]).status, 1));
  // A certified user theorem gets the kernel's native flag, but must not be
  // mistaken for Base's marker and shrink a user datatype to builtin Bool.
  const shadow = path.join(TEMP, "native_marker.bend");
  fs.writeFileSync(shadow, `
type Bool is Data:
  False{}
  True{}
  Third{}
law Nat.add: {True{} == True{} : Bool}
def collapse(b: Bool) -> Bool:
  match b:
    case False{}: False{}
    case True{}: True{}
    case Third{}: False{}
law bogus:
  for b: Bool
  {collapse(b) == b : Bool}
`);
  const shadowed = run([shadow]);
  check(() => assert.equal(shadowed.status, 1));
  check(() => assert.match(shadowed.stderr, /could not prove bogus/));

  const program = file("program", `
law zero:
  for n: Nat
  {Nat.add(n, 0n) == n : Nat}
def value(n: Nat) -> Nat:
  %p@zero(n) : Nat
  42n
def fact(n: Nat) -> {Nat.add(n, 0n) == n : Nat}: zero(n)
def main() -> Nat: value(3n)
`);
  const interp = run([program]);
  check(() => assert.equal(interp.status, 0, interp.stderr));
  check(() => assert.equal(interp.stdout.trim(), "42n"));
  const js = path.join(TEMP, "program.js"), c = path.join(TEMP, "program.c");
  const build = run([program, "-o", js, "-o", c]);
  check(() => assert.equal(build.status, 0, build.stderr));
  const executed = child.spawnSync(process.execPath, [js], { encoding: "utf8", timeout: 10000 });
  check(() => assert.equal(executed.status, 0, executed.stderr));
  check(() => assert.equal(executed.stdout.trim(), "42n"));
  check(() => assert.ok(fs.readFileSync(c, "utf8").includes("int main(")));
  const loader = child.spawnSync(process.execPath, [...NODE,
    ...(process.versions.bun ? ["--preload", CLI] : ["--import", CLI]), "--eval",
    `import B from ${JSON.stringify(program)}; console.log(B.value(3n).toString())`],
    { encoding: "utf8", env, timeout: 30000 });
  check(() => assert.equal(loader.status, 0, loader.stderr));
  check(() => assert.equal(loader.stdout.trim(), "42"));

  const opaque = file("opaque", `
law witness:
  exs n: Nat
  {n == 0n : Nat}
def extract(w: Exists(Nat, n => {n == 0n : Nat})) -> Nat:
  match w:
    case Tuple{n, p}: n
def main() -> Nat: extract(witness)
`);
  const o = await read(opaque);
  await Why3.check_book(o.book, options); // Usable logically, without a runtime witness.
  check(() => assert.equal(Why3.evidence(o.book).length, 1));
  const stuck = run([opaque]);
  check(() => assert.equal(stuck.status, 1));
  check(() => assert.match(stuck.stderr, /cannot execute opaque theorem/));
  check(() => assert.equal(run([opaque, "-o", path.join(TEMP, "opaque.js")]).status, 1));

  const session = path.join(TEMP, "session.mlw");
  const proof = run([path.join(ROOT, "demos/proof_why3/PROOF.bend"), "--prove", "-o", session]);
  check(() => assert.equal(proof.status, 0, proof.stderr));
  check(() => assert.ok(!proof.stdout.includes("42n")));
  check(() => assert.match(fs.readFileSync(session, "utf8"), /axiom Fact_/));
  const typed = child.spawnSync(WHY3, ["prove", "--type-only", session], { encoding: "utf8", timeout: 10000 });
  check(() => assert.equal(typed.status, 0, typed.stderr));
  const replay = child.spawnSync(WHY3, ["prove", "--json", "-P", PROVER, "-t", "1", "-a", "induction_ty_lex", session],
    { encoding: "utf8", timeout: 30000 });
  check(() => assert.equal(replay.status, 0, replay.stderr));
  check(() => assert.ok(Why3.read_answers(replay.stdout).every((a) => a.answer === "Valid")));

  const changed = file("changed", "def f(n: Nat) -> Nat: n\nlaw identity:\n  for n: Nat\n  {f(n) == n : Nat}");
  check(() => assert.equal(run([changed]).status, 0));
  fs.writeFileSync(changed, fs.readFileSync(changed, "utf8").replace("Nat: n", "Nat: Succ{n}"));
  check(() => assert.equal(run([changed]).status, 1));
  const aggregate = path.join(TEMP, "checkup.bend");
  fs.writeFileSync(aggregate, "import ./program.bend as Program\n");
  check(() => assert.equal(run([aggregate, "--checkup"]).status, 0));
  const missing = run([program, "--why3-bin", path.join(TEMP, "missing")]);
  check(() => assert.equal(missing.status, 1));
  check(() => assert.match(missing.stderr, /Install Why3/));
}

try {
  await orchestration();
  await strategies();
  await parallel_goals();
  await batches();
  const available = child.spawnSync(WHY3, ["--version"], { encoding: "utf8" }).status === 0;
  if (!available && process.argv.includes("--require-prover")) throw new Error("Why3 is required for this gate");
  if (available) await actual_proofs();
  console.log("PASS: " + checks + " integrated proof checks" + (available ? " (including real Why3 proofs)" : " (real proofs SKIPPED)"));
} catch (e) {
  console.error((e as Bend.Err)?.$ === "Err" ? Bend.err_show(e as Bend.Err) : e);
  process.exitCode = 1;
} finally {
  fs.rmSync(TEMP, { recursive: true, force: true });
}
