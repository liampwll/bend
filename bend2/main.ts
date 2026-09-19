#!/usr/bin/env bun
// Run, this file is the CLI. Imported, it is the loader that makes `import
// Game from "./x.bend"` work: a bun plugin (preload it in bunfig.toml, list
// it under [serve.static] plugins, or hand it to Bun.build) and a node hook
// (node --import). A .bend module exports every filled, non-base, non-IO
// def, wrapped so a JS caller passes the live arguments, in one call or
// curried, and gets a plain value back: a constructor is {$: "Name", field:
// value, ...}, a closure is a function, Nat is BigInt, Bool, String and U32
// are native. A page bundles through Bun.build with the loader on, since
// the bun build CLI takes no plugins.

import * as child from "node:child_process";
import * as crypto from "node:crypto";
import * as fs from "node:fs";
import * as mod from "node:module";
import * as os from "node:os";
import * as path from "node:path";
import * as url from "node:url";
import * as thr from "node:worker_threads";

import type { BunPlugin } from "bun";

import * as Bend from "./bend.ts";
import * as Comp from "./comp.ts";
import * as Why3 from "./why3.ts";

// Main
// ====

// Constants
// =========

const VERSION = "2.0.16";

const HELP = `Bend ${VERSION}: check, run, build and publish Bend programs.

usage:
  bend <file.bend> [args]     check (Why3 discharges open laws), then run main
                              (IO.args; a "--" ends bend's own options)
  bend <file.bend> -o <out>   build a binary; <out>.c emits C, <out>.js JS
  bend <file.bend> --checkup  check and run each import alone
  bend <file.bend> --publish  publish the file and its imports to the hub
  bend <file.bend> --why3    export laws as WhyML (stdout, or -o <file.mlw>)
  bend <file.bend> --prove   check all proofs without running main
    -o <file.mlw>            save the discharged Why3 tasks for inspection
    --kernel-only            disable automatic Why3 proof checking
    --law <name>             standalone law selection with --why3/--prove
    --prover <name>          Why3 prover/shortcut (repeatable; default alt-ergo)
    --timeout <seconds>      time per goal/prover (default 1; standalone: 5)
    --jobs <count>           maximum concurrent Why3/prover attempts (1-64)
    --induct <variable>      select a variable for induction (repeatable)
    --why3-bin <path>        Why3 executable (default why3)
    --why3-config <file>     Why3 prover configuration
  bend <page.html> -o <dir>   bundle a page that imports .bend files
  bend base [--types|<name>]  print Base, its types, or a name and its subnames
  bend guide                  print the Bend guide
  bend update                 install the latest bend (curl | sh, shown first)
  bend --version              print the version

Read the guide (\`bend guide\`) before writing Bend code.
`;

const BASE = Bend.BASE_BEND;

const GUIDE = path.join(Bend.BEND_DIR, "..", "guide");

const ORIGIN = process.env.BEND_ORIGIN ?? "https://bend-lang.com";

// the daily version check's cache: when it last asked, and the answer
const CHECK = path.join(os.homedir(), ".bend", "check.json");

const DAY = 86400000;

// A package's proof of work is a nonce whose sha256(hash + " " + nonce)
// opens (its top 53 bits) with a number under 2^53 / work, where work is
// POW hashes (two seconds of an M4 Max's sixteen cores) per 256 KiB of
// package, and no less. Every core mines; the hub checks it with one hash.
const POW = 140000000;

const POW_JS = `
const crypto = require("node:crypto");
const { parentPort, workerData: { pre, lim, from, step } }
  = require("node:worker_threads");
for (let n = from;; n += step) {
  const h = crypto.hash("sha256", pre + n, "buffer");
  if ((h[0] * 16777216 + (h[1] << 16) + (h[2] << 8) + h[3]) * 2097152
    + ((h[4] * 16777216 + (h[5] << 16) + (h[6] << 8) + h[7]) >>> 11) < lim) {
    parentPort.postMessage(n);
    break;
  }
}`;

function plugin(checking: Why3.CheckOptions = {}): BunPlugin {
  return {
    name: "bend",
    setup(build) {
      build.onLoad({ filter: /\.bend$/ }, async (args) =>
        ({ contents: await load_js(args.path, checking), loader: "js" }));
    },
  };
}
const PLUGIN = plugin();

// CLI
// ===

// cli runs the command, then (not after --version or update) the daily
// version check, so the check never delays the command's own work.
async function cli(): Promise<void> {
  const args = process.argv.slice(2);
  if (args[0] === "--version" && args.length === 1) {
    return cli_say(1, "bend " + VERSION + "\n");
  }
  if (args[0] === "update" && args.length === 1) {
    return cli_update();
  }
  if (args[0] === "guide" && args.length <= 2) {
    cli_guide(args[1] ?? "guide");
  } else if (args[0] === "base" && args.length <= 2) {
    cli_base(args[1]);
  } else {
    await cli_file(args);
  }
  await check();
}

// cli_guide prints guide/<NAME>.md: the guide, or a named extra.
function cli_guide(name: string): void {
  const file = path.join(GUIDE, name.toUpperCase() + ".md");
  if (!fs.existsSync(file)) {
    cli_fail("no guide named " + name);
  }
  cli_say(1, fs.readFileSync(file, "utf8"));
}

// cli_update runs the installer again: the one way bend changes. The
// command prints first, so the user can run it alone.
function cli_update(): void {
  const cmd = "curl -fsSL " + ORIGIN + "/install.sh | sh";
  cli_say(2, cmd + "\n");
  process.exitCode = child.spawnSync("sh", ["-c", cmd],
    { stdio: "inherit" }).status ?? 1;
}

// check is the whole telemetry: once a day, a GET of /check?v=&os=&arch=
// (nothing else: no id, no command, no timing) whose answer {ver, notice}
// is cached in CHECK; a cached ver newer than this one prints one line on
// stderr, and the notice. The cache is stamped before the request, so a
// day has one request whatever happens to it; BEND_NO_TELEMETRY=1 skips
// everything; the check never fails the command.
async function check(): Promise<void> {
  if (process.env.BEND_NO_TELEMETRY) {
    return;
  }
  let last = { t: 0, ver: VERSION, notice: "" };
  try {
    last = { ...last, ...JSON.parse(fs.readFileSync(CHECK, "utf8")) };
  } catch {}
  try {
    if (Date.now() - last.t > DAY) {
      last.t = Date.now();
      fs.mkdirSync(path.dirname(CHECK), { recursive: true });
      fs.writeFileSync(CHECK, JSON.stringify(last) + "\n");
      const res = await fetch(ORIGIN + "/check?v=" + VERSION + "&os="
        + process.platform + "&arch=" + process.arch, { headers: { "User-Agent":
        "bend/" + VERSION }, signal: AbortSignal.timeout(3000) });
      const got = await res.json() as { ver?: unknown; notice?: unknown };
      last.ver = typeof got.ver === "string" ? got.ver : VERSION;
      last.notice = typeof got.notice === "string" ? got.notice : "";
      fs.writeFileSync(CHECK, JSON.stringify(last) + "\n");
    }
  } catch {}
  if (ver_newer(last.ver)) {
    cli_say(2, "bend " + last.ver + " is available: run bend update\n"
      + (last.notice === "" ? "" : last.notice.replace(/[\x00-\x1f\x7f]/g, "")
      .slice(0, 200) + "\n"));
  }
}

function ver_newer(ver: string): boolean {
  const a = ver.split(".").map(Number);
  const b = VERSION.split(".").map(Number);
  return a.length === 3 && a.every(Number.isInteger)
    && (a[0] - b[0] || a[1] - b[1] || a[2] - b[2]) > 0;
}

// cli_file checks, runs, builds, publishes or bundles a file
async function cli_file(args: string[]): Promise<void> {
  const outs: string[] = [];
  const argv: string[] = [];
  let file: string | undefined;
  let checkup = false;
  let publish = false;
  let why3 = false;
  let prove = false;
  let kernelOnly = false;
  const laws: string[] = [], provers: string[] = [], induct: string[] = [];
  const proof: Why3.ProveOptions = { provers };
  for (let i = 0; i < args.length; i += 1) {
    const a = args[i];
    if (a === "--help" || a === "-h") {
      return cli_say(1, HELP);
    } else if (a === "--checkup") {
      checkup = true;
    } else if (a === "--publish") {
      publish = true;
    } else if (a === "--why3" || a === "--prove") {
      why3 ||= a === "--why3";
      prove ||= a === "--prove";
    } else if (a === "--kernel-only") {
      kernelOnly = true;
    } else if (["--law", "--prover", "--timeout", "--jobs", "--induct", "--why3-bin", "--why3-config"].includes(a)) {
      const value = args[++i];
      if (value === undefined || value.startsWith("--")) cli_fail(a + " needs a value");
      if (a === "--law") laws.push(value);
      if (a === "--prover") provers.push(value);
      if (a === "--induct") induct.push(value);
      if (a === "--why3-bin") proof.binary = value;
      if (a === "--why3-config") proof.config = value;
      if (a === "--jobs") {
        proof.jobs = Number(value);
        if (!/^\d+$/.test(value) || proof.jobs < 1 || proof.jobs > 64) {
          cli_fail("--jobs must be an integer from 1 to 64");
        }
      }
      if (a === "--timeout") {
        proof.timeout = Number(value);
        if (!/^\d+$/.test(value) || proof.timeout < 1 || proof.timeout > 3600) {
          cli_fail("--timeout must be an integer from 1 to 3600 seconds");
        }
      }
    } else if (a === "-o") {
      i += 1;
      outs.push(args[i] ?? cli_fail("-o needs an output file"));
    } else if (a === "--") {
      argv.push(...args.splice(i + 1));
    } else if (a.startsWith("-")) {
      cli_fail("unknown option " + a);
    } else if (file !== undefined) {
      argv.push(a);
    } else {
      file = a;
    }
  }
  if (file === undefined) {
    cli_say(1, HELP);
    process.exit(1);
  }
  if (laws.length && !why3 && !prove) cli_fail("--law selects standalone --why3 or --prove goals");
  why3 ||= laws.length > 0 || (!prove && outs.some((out) => /\.(mlw|why)$/.test(out)));
  if (kernelOnly && (why3 || prove)) cli_fail("--kernel-only cannot be combined with --why3 or --prove");
  const checking: Why3.CheckOptions = { ...proof, induct, kernelOnly };
  if ((why3 || prove) && (checkup || publish || file.endsWith(".html") || outs.length > 1)) {
    cli_fail("Why3 takes one Bend file and at most one output, without --checkup or --publish");
  }
  if ((why3 || prove) && outs.some((out) => !/\.(mlw|why)$/.test(out))) {
    cli_fail("Why3 output must end in .mlw or .why");
  }
  if (file.endsWith(".html")) {
    if (outs.length !== 1 || checkup || publish) {
      cli_fail("a page bundles with -o <dir>");
    }
    return cli_bundle(file, outs[0], checking);
  }
  if (publish && (outs.length !== 0 || checkup)) {
    cli_fail("--publish takes no other option");
  }
  if (argv.length !== 0 && (outs.length !== 0 || checkup || publish || why3 || prove)) {
    cli_fail("arguments go to a run: bend <file.bend> [args]");
  }
  if (checkup && outs.length !== 0) {
    cli_fail("--checkup takes no -o: a binary holds one main, so build each"
      + " import alone");
  }
  try {
    if (why3) {
      return await cli_why3(file, outs[0], prove, { laws, induct }, proof);
    }
    if (prove) {
      const seen = new Map<string, string | null>();
      const book = await book_read(file, undefined, seen, checking);
      if (outs[0] !== undefined) {
        why3_output(book, seen, outs[0], checking.config);
        fs.writeFileSync(outs[0], Why3.export_session(book));
      }
      cli_report(book, 1);
      return cli_proof_report(book);
    }
    if (publish) {
      return await cli_publish(file, checking);
    }
    if (checkup) {
      return await cli_checkup(file, checking);
    }
    const seen = new Map<string, string | null>();
    const book = await book_read(file, undefined, seen, checking);
    if (outs.length !== 0 || book_main(book) !== null) {
      cli_report(book, 2);
    }
    if (outs.length === 0) {
      process.exitCode = book_run(book, argv);
      return;
    }
    cli_proof_report(book, 2);
    const ins = new Set([...seen.keys(), ...Object.values(book.tlds).flatMap((t) =>
      t.$ === "Def" && t.i !== undefined ? t.i.map(path_real) : [])]);
    if (checking.config !== undefined) ins.add(path_real(checking.config));
    for (const out of outs) {
      const at = path_real(out);
      if (ins.has(at) || (fs.existsSync(at) && fs.statSync(at).isDirectory())) {
        cli_fail("-o " + out + " is a file the program reads, or a directory");
      }
      cli_emit(book, out);
    }
  } catch (e) {
    cli_say(2, book_err(e) + "\n");
    process.exitCode = 1;
  }
}

async function cli_why3(file: string, out: string | undefined, run: boolean,
  options: Why3.ExportOptions, proof: Why3.ProveOptions): Promise<void> {
  const seen = new Map<string, string | null>();
  const book = Bend.book_nil();
  await Bend.book_load(book, file, "", seen);
  const exported = Why3.export_book(book, { ...options, files: seen });
  let dir: string | undefined;
  if (out !== undefined) {
    why3_output(book, seen, out, proof.config);
    fs.writeFileSync(out, exported.source);
  } else if (!run) {
    return cli_say(1, exported.source);
  } else {
    dir = fs.mkdtempSync(path.join(os.tmpdir(), "bend-why3-"));
    out = path.join(dir, "laws.mlw");
    fs.writeFileSync(out, exported.source);
  }
  if (!run) return;
  let failed = false;
  try {
    const results = await Why3.prove(path.resolve(out!), exported.goals, proof);
    for (const r of results) {
      const at = (r.goal.file ?? file) + (r.goal.line === undefined ? "" : ":" + r.goal.line);
      cli_say(1, at + ": " + r.goal.name + ": " + (r.valid ? "proved" : "unproved")
        + " (" + r.attempts.map((a) => a.prover + ": " + a.answer.replace(/\s+/g, " ")).join(", ") + ")\n");
      failed ||= !r.valid;
    }
    cli_say(1, results.filter((r) => r.valid).length + "/" + results.length + " laws proved by Why3.\n");
  } finally {
    if (dir !== undefined) fs.rmSync(dir, { recursive: true, force: true });
  }
  if (failed) process.exitCode = 1;
}

function why3_output(book: Bend.Book, seen: Map<string, string | null>, out: string, config?: string): void {
  const at = path_real(out);
  const inputs = new Set([...seen.keys(), ...Object.values(book.tlds).flatMap((t) =>
    t.$ === "Def" && t.i !== undefined ? t.i.map(path_real) : [])]);
  config ??= process.env.WHY3CONFIG;
  if (config !== undefined) inputs.add(path_real(config));
  if (inputs.has(at) || (fs.existsSync(at) && fs.statSync(at).isDirectory())) {
    cli_fail("-o " + out + " is a file the program reads, or a directory");
  }
}

// cli_checkup checks and runs each import of the file alone (Base read
// once, seeded into every module that imports it); one that fails fails it.
async function cli_checkup(file: string, checking: Why3.CheckOptions): Promise<void> {
  const base = await book_read(BASE, undefined, undefined, checking);
  let bad = false;
  for (const raw of fs.readFileSync(file, "utf8").split("\n")) {
    const m = /^import\s+(\S+)\s+as\s+[A-Za-z_][A-Za-z0-9_]*\s*$/
      .exec(raw.trim());
    if (m === null) {
      continue;
    }
    const at = path.join(path.dirname(file), m[1]);
    cli_say(1, "--- " + m[1] + " ---\n");
    let code = 1;
    try {
      const own = /^import Base$/m.test(fs.readFileSync(at, "utf8"));
      code = book_run(await book_read(at, own ? base : undefined, undefined, checking), []);
    } catch (e) {
      cli_say(2, book_err(e) + "\n");
    }
    if (code !== 0) {
      cli_say(1, "exit " + String(code) + "\n");
      bad = true;
    }
  }
  if (bad) {
    process.exit(1);
  }
}

function path_real(p: string): string {
  return fs.existsSync(p) ? fs.realpathSync(p) : path.resolve(p);
}

function cli_emit(book: Bend.Book, out: string): void {
  book = Why3.runtime_book(book);
  if (out.endsWith(".js")) {
    fs.writeFileSync(out, Comp.js_book(book));
  } else if (out.endsWith(".c")) {
    fs.writeFileSync(out, Comp.compile_book(book));
  } else {
    const dir = fs.mkdtempSync(path.join(os.tmpdir(), "bend-"));
    const c   = path.join(dir, path.basename(out) + ".c");
    fs.writeFileSync(c, Comp.compile_book(book));
    try {
      cli_build(out, c);
    } finally {
      fs.rmSync(dir, { recursive: true, force: true });
    }
  }
}

// cc_find is the first of $CC, clang and every clang-NN on PATH (newest
// first) that is new enough: clang 14 for a CPU build, and for a GPU build
// clang 19 (Apple clang 17, which ships LLVM 19), whose #embed
// carries the device program.
function cc_find(gpu: boolean): string {
  function dir_list(dir: string): string[] {
    try {
      return fs.readdirSync(dir);
    } catch {
      return [];
    }
  }
  const dirs = (process.env.PATH ?? "").split(path.delimiter);
  const nums = [...new Set(dirs.flatMap(dir_list).filter((f) =>
    /^clang-\d+$/.test(f)))].sort((a, b) => Number(b.slice(6)) - Number(a.slice(6)));
  const olds: string[] = [];
  const ccs  = [...(process.env.CC ? [process.env.CC] : []), "clang", ...nums];
  for (const cc of ccs) {
    const out = child.spawnSync(cc, ["--version"], { encoding: "utf8" }).stdout ?? "";
    const m   = /^(Apple )?(?:\w+ )?clang version (\d+)/m.exec(out);
    const need = gpu ? (m?.[1] === undefined ? 19 : 17) : 14;
    if (m !== null && Number(m[2]) >= need) {
      return cc;
    }
    olds.push(m !== null ? "clang " + m[2] + " as " + cc
      : out ? cc + ", which is not clang" : "no " + cc);
  }
  throw "Error: bend needs clang " + (gpu ? "19 (Apple clang 17)" : "14")
    + " or newer to build " + (gpu ? "a GPU program" : "binaries") + " (found "
    + olds.join(", ") + "); on Debian/Ubuntu: curl -fsSL"
    + " https://apt.llvm.org/llvm.sh | sudo bash -s 19; on macOS: xcode-select"
    + " --install";
}

// cli_build builds the C file at `file` into the binary `bin`. A `!` program
// builds with the GPU lane and writes its GPU program too (on Linux only with
// CUDA at $CUDA_HOME, else at /usr/local/cuda, its libraries in lib64 or, as
// nix lays them, lib; else the ! runs on the cores). On macOS a program with
// a framework (#import: a window, audio) builds as Objective-C; on Linux it
// links the X11 and ALSA libraries it includes.
function cli_build(bin: string, file: string): void {
  const c     = fs.readFileSync(file, "utf8");
  const mac   = process.platform === "darwin";
  const cuda  = process.env.CUDA_HOME || "/usr/local/cuda";
  const bangs = !/^#define BANGS\s+0$/m.test(c)
    && (mac || fs.existsSync(cuda + "/include/nvrtc.h"));
  const cc    = cc_find(bangs);
  const objc  = mac && (bangs || /^#import /m.test(c))
    ? ["-x", "objective-c", "-fobjc-arc", "-fmodules"] : [];
  const libs  = [["X11", "X11"], ["alsa", "asound"]].flatMap(([h, l]) =>
    !mac && c.includes("#include <" + h + "/") ? ["-l" + l] : []);
  const cpu = [...objc, "-std=c11", "-O3", file, "-lpthread", "-lm",
    ...libs, "-o", path.resolve(bin)];
  const gpu = mac ? ["-DBEND_METAL=1", ...cpu]
    : ["-DBEND_CUDA=1", "-I" + cuda + "/include", "-L" + cuda + "/lib64",
      "-L" + cuda + "/lib", ...cpu, "-lcuda", "-lnvrtc"];
  const steps: [string, string[]][] = bangs
    ? [[cc, gpu], [path.resolve(bin), ["--gpu-build"]]] : [[cc, cpu]];
  for (const [cmd, args] of steps) {
    if (child.spawnSync(cmd, args, { stdio: "inherit" }).status !== 0) {
      throw "Error: " + path.basename(cmd) + " failed to build " + bin;
    }
  }
}

// cli_base prints the base library; with --types, its type declarations
// (every `type`, and every law whose result is a kind); with a name, the
// blocks declaring it or a name under it (its law, its def, its @unsafe).
function cli_base(what?: string): void {
  const src = fs.readFileSync(BASE, "utf8");
  if (what === undefined) {
    return cli_say(1, src);
  }
  const want: string[] = [];
  for (const text of src.split(/\n(?=type |law |def |@)/)) {
    const m = /^(type|law|def) ([^\s(<:]+)/m.exec(text);
    if (m === null) {
      continue;
    }
    const s = text.replace(/(\n(#[^\n]*)?)+$/, "");
    const last = s.slice(s.lastIndexOf("\n") + 1);
    const ok = what === "--types"
      ? m[1] === "type" || (m[1] === "law" && /^ *(Type|Data|Kind\(.*\))$/.test(last))
      : m[2] === what || m[2].startsWith(what + ".");
    if (ok) {
      want.push(s);
    }
  }
  if (want.length === 0) {
    cli_fail("Base has no " + what);
  }
  cli_say(1, want.join("\n\n") + "\n");
}

async function cli_bundle(page: string, dir: string, checking: Why3.CheckOptions): Promise<void> {
  const out = await Bun.build({
    entrypoints: [page],
    outdir: dir,
    target: "browser",
    minify: true,
    plugins: [plugin(checking)],
  });
  for (const a of out.outputs) {
    cli_say(1, a.path + " (" + (a.size / 1024).toFixed(1) + "kb)\n");
  }
}

// Publish
// =======

// cli_publish checks the file, then posts what the loader read (no TODO
// left) to the hub with its proof of work, and prints the import line.
async function cli_publish(file: string, checking: Why3.CheckOptions): Promise<void> {
  const seen = new Map<string, string | null>();
  const book = await book_read(file, undefined, seen, checking);
  cli_report(book, 2);
  cli_proof_report(book, 2);
  const files = pkg_files(file, book, seen);
  const entry = Object.keys(files)[0];
  const name  = path.basename(entry, ".bend");
  if (name === "") {
    cli_fail("a published file needs a name before .bend");
  }
  const paths = Object.keys(files).sort();
  const bytes = paths.reduce((n, p) => n + Buffer.byteLength(files[p]), 0);
  const hash  = "0x" + sha256(paths.map((p) => sha256(files[p]) + " " + p
    + "\n").join("")).slice(0, 32);
  cli_say(2, "publishing " + String(paths.length) + " files, "
    + String(bytes) + " bytes, as " + hash + " (mining its proof of work)\n");
  const nonce = await pow_mine(hash, bytes);
  const res = await fetch(Bend.BEND_HUB, { method: "POST",
    body: JSON.stringify({ files, nonce }) });
  const got = (await res.text()).trim();
  if (!res.ok || got !== hash) {
    throw "Error: " + Bend.BEND_HUB + " answered: " + got;
  }
  cli_say(1, hash + "\nimport " + hash + "/" + entry + " as "
    + name[0].toUpperCase() + name.slice(1) + "\n");
}

// pkg_files is the package the loader read for this file, the entry first:
// every .bend file at its namespace (the entry at its name), every foreign
// .c or .js file at its path from the entry's directory; base and the
// store's packages stay out. A path that climbs above the entry's directory
// takes the entry's ancestor directories along, as many as the deepest climb.
function pkg_files(file: string, book: Bend.Book,
  seen: Map<string, string | null>): Record<string, string> {
  const dir  = file.slice(0, file.lastIndexOf("/") + 1);
  const raws = [...[...seen].flatMap(([real, ns]): [string, string][] =>
    real === BASE || ns === null || ns.startsWith("0x") ? []
      : [[ns === "" ? path.basename(file) : ns + ".bend", real]]),
  ...Object.entries(book.tlds).flatMap(([k, tld]): [string, string][] =>
    tld.$ !== "Def" || tld.i === undefined || tld.b === true
      || k.startsWith("0x") ? [] : tld.i.map((f) =>
      [f.startsWith(dir) ? f.slice(dir.length) : f, f]))];
  const ups = raws.map(([p]) => path.posix.normalize(p).split("/")
    .filter((s) => s === "..").length);
  const anc = fs.realpathSync(path.dirname(file)).split("/")
    .slice(-Math.max(0, ...ups) || Infinity);
  const files: Record<string, string> = {};
  for (const [raw, real] of raws) {
    const p = path.posix.join(...anc, raw);
    if (p.startsWith("/") || p.startsWith("..")) {
      throw "Error: " + real + " cannot be published (an absolute import,"
        + " or a climb above the file system)";
    }
    files[p] = fs.readFileSync(real, "utf8");
  }
  return files;
}

function sha256(text: string): string {
  return crypto.createHash("sha256").update(text).digest("hex");
}

async function pow_mine(hash: string, bytes: number): Promise<number> {
  const step = os.availableParallelism();
  const lim  = 2 ** 53 / (POW * Math.max(1, bytes / 262144));
  const ws   = Array.from({ length: step }, (_, k) => new thr.Worker(POW_JS,
    { eval: true, workerData: { pre: hash + " ", lim, from: k, step } }));
  const n = await new Promise<number>((res) =>
    ws.forEach((w) => w.on("message", res)));
  ws.forEach((w) => w.terminate());
  return n;
}

// Report
// ======

// cli_report prints the unsafe count: the verdict of a check on stdout, a
// note before a run, an emit or a publish on stderr (silent at zero).
function cli_report(book: Bend.Book, fd: number): void {
  const uns  = Object.entries(book.tlds).filter(([k, t]) =>
    t.$ === "Def" && (t.u === true || k.includes("~"))).length;
  if (uns > 0) {
    cli_say(fd, `All terms check, with ${uns} unsafe annotation`
      + `${uns === 1 ? "" : "s"}.\n`);
  } else if (fd === 1) {
    cli_say(1, "All terms check.\n");
  }
}

function cli_proof_report(book: Bend.Book, fd = 1): void {
  const n = Why3.evidence(book).length;
  if (n > 0) cli_say(fd, "Why3 proved " + n + " obligation" + (n === 1 ? "" : "s")
    + " (trusted ATP evidence).\n");
}

function cli_say(fd: number, text: string): void {
  try {
    fs.writeSync(fd, text);
  } catch (e) {
    if ((e as NodeJS.ErrnoException).code !== "EPIPE") {
      throw e;
    }
    process.exit(0);
  }
}

function cli_fail(msg: string): never {
  cli_say(2, "bend: " + msg + " (see bend --help)\n");
  process.exit(1);
}

// Book
// ====

async function book_read(file: string, base?: Bend.Book,
  seen = new Map<string, string | null>(), checking: Why3.CheckOptions = {}): Promise<Bend.Book> {
  const book = base === undefined ? Bend.book_nil() : book_seed(base);
  if (base !== undefined) {
    seen.set(BASE, "");
  }
  await Bend.book_load(book, file, "", seen);
  const laws = path.join(path.dirname(file), "LAWS.bend");
  if (path.basename(file) === "PROOF.bend" && fs.existsSync(laws)
    && !seen.has(fs.realpathSync(laws))) {
    cli_fail("PROOF.bend must import ./LAWS.bend");
  }
  await Why3.check_book(book, { ...checking, files: seen }, base?.order.length ?? 0);
  return book;
}

function book_seed(base: Bend.Book): Bend.Book {
  const book = Bend.book_nil();
  for (const k of Object.keys(base.tlds)) {
    book.tlds[k] = { ...base.tlds[k] };
  }
  Object.assign(book.ctrs, base.ctrs);
  for (const k of Object.keys(base.tmps)) {
    book.tmps[k] = { ...base.tmps[k], p: { ...base.tmps[k].p, book },
      is: { ...base.tmps[k].is } };
  }
  book.order.push(...base.order);
  return book;
}

function book_main(book: Bend.Book): Bend.Def | null {
  const main = book.tlds["main"];
  return main === undefined || main.$ !== "Def"
    || (main.v === null && main.i === undefined) ? null : main;
}

function book_run(book: Bend.Book, argv: string[]): number {
  const main = book_main(book);
  if (main === null) {
    cli_report(book, 1);
    cli_proof_report(book);
    return 0;
  }
  cli_proof_report(book, 2);
  book = Why3.runtime_book(book);
  if (Comp.io_type(book) !== null) {
    return Comp.io_run(book, argv);
  }
  const snf = Bend.term_snf(book, (book.tlds["main"] as Bend.Def).v as Bend.HTerm);
  Why3.executable_value(book, snf);
  cli_say(1, Bend.term_show(Bend.term_lower(snf)) + "\n");
  return 0;
}

function book_err(e: unknown): string {
  const err = e as Bend.Err;
  if (e instanceof RangeError) {
    return "Error: the machine stack overflowed (a deep recursion, or a"
      + " literal too large to expand)";
  }
  return err?.$ === "Err" ? Bend.err_show(err) : String(e);
}

// Load
// ====

async function load_js(path: string, checking: Why3.CheckOptions = {}): Promise<string> {
  let book: Bend.Book;
  try {
    book = await book_read(path, undefined, undefined, checking);
  } catch (e) {
    throw new Error(book_err(e));
  }
  const outs = [...new Set(book.order)].filter((k) => {
    const tld = book.tlds[k];
    return tld.$ === "Def" && tld.v !== null && tld.b !== true
      && tld.i === undefined && Comp.io_base(book, tld.T) === null;
  });
  return Comp.js_lib(Why3.runtime_book(book), outs, outs);
}

export async function load(u: string, context: unknown,
  next: (u: string, context: unknown) => unknown): Promise<unknown> {
  return u.endsWith(".bend")
    ? { format: "module", shortCircuit: true,
      source: await load_js(url.fileURLToPath(u)) }
    : next(u, context);
}

export default PLUGIN;

if (import.meta.main) {
  if (typeof Bun === "undefined") {
    cli_say(2, "bend runs on Bun: curl -fsSL https://bend-lang.com/install.sh"
      + " | sh\n");
    process.exit(1);
  }
  await cli();
  process.exit();
} else if (typeof Bun !== "undefined") {
  Bun.plugin(PLUGIN);
} else if (thr.isMainThread) {
  mod.register(import.meta.url);
}
