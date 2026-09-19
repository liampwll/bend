#!/usr/bin/env bun
// Local Why3 gate. Node 24+ also runs the API checks; CLI checks need Bun.
// No cluster is needed. --require-prover requires a Why3 installation.

import * as assert from "node:assert/strict";
import * as child from "node:child_process";
import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import * as Bend from "../bend2/bend.ts";
import * as Why3 from "../bend2/why3.ts";

const ROOT = path.resolve(import.meta.dirname, "..");
const TEMP = fs.mkdtempSync(path.join(os.tmpdir(), "bend-why3-test-"));
const CLI = path.join(ROOT, "bend2/main.ts");
const BUN = process.versions.bun ? process.execPath : process.env.BUN ?? "bun";
const WHY3 = process.env.WHY3 ?? "why3";
const PROVER = process.env.WHY3_PROVER ?? "alt-ergo";
let checks = 0;

function check(f: () => void): void { f(); checks++; }

function cli(args: string[]) {
  return child.spawnSync(BUN, [CLI, ...args],
    { cwd: ROOT, env: { ...process.env, BEND_NO_TELEMETRY: "1" }, encoding: "utf8", timeout: 30000 });
}

async function read(file: string): Promise<{ book: Bend.Book; files: Map<string, string | null> }> {
  const book = Bend.book_nil();
  const files = new Map<string, string | null>();
  await Bend.book_load(book, file, "", files);
  return { book, files };
}

function answer(name: string, result = "Valid"): string {
  return JSON.stringify({ term: { goal_name: name }, "prover-result": { answer: result, time: 0.01 } }, null, 2);
}

async function fake_tests(): Promise<void> {
  const goal = { name: "sample", id: "Law_sample" };
  check(() => assert.deepEqual(Why3.read_answers(answer(goal.id) + "\n" + answer("other", "Unknown")), [
    { name: goal.id, answer: "Valid", time: 0.01 }, { name: "other", answer: "Unknown", time: 0.01 },
  ]));
  for (const s of ["Valid", "{", "{}", answer(goal.id) + "trailing", '{"prover-result":{"answer":"Valid"}}']) {
    check(() => assert.throws(() => Why3.read_answers(s)));
  }
  // The binary path deliberately contains a space. Arguments must be passed
  // directly, without shell interpolation; portfolio attempts select goals.
  const binary = path.join(TEMP, "why3 tool");
  function stub(stdout: string, code = 0): void {
    fs.writeFileSync(binary, "#!/usr/bin/env node\nprocess.stdout.write(" + JSON.stringify(stdout)
      + "); process.exitCode = " + code + ";\n", { mode: 0o755 });
  }
  for (const [out, code] of [["", 0], [answer("other"), 0], [answer(goal.id) + answer(goal.id), 0],
    [answer(goal.id), 1], [answer(goal.id), 2]] as const) {
    stub(out, code);
    await assert.rejects(() => Why3.prove("space in filename.mlw", [goal], { binary }));
    checks++;
  }
  stub(answer(goal.id, "Timeout"), 2);
  assert.equal((await Why3.prove("unused.mlw", [goal], { binary }))[0].valid, false);
  checks++;
  stub(answer(goal.id));
  assert.equal((await Why3.prove("unused.mlw", [goal], { binary }))[0].valid, true);
  checks++;
  for (const timeout of [0, -1, 0.5, Infinity, NaN, 3601]) {
    await assert.rejects(() => Why3.prove("unused.mlw", [goal], { binary, timeout }));
    checks++;
  }
  await assert.rejects(() => Why3.prove("unused.mlw", [], { binary }));
  await assert.rejects(() => Why3.prove("unused.mlw", [goal], { binary: path.join(TEMP, "missing") }));
  checks += 2;
  fs.writeFileSync(binary, `#!/usr/bin/env node
const args = process.argv.slice(2);
const prover = args[args.indexOf('-P') + 1];
const goals = args.flatMap((x,i) => x === '-G' ? [args[i+1]] : []);
for (const name of goals) {
  const valid = prover === 'second' || name === 'Law_sample';
  console.log(JSON.stringify({term:{goal_name:name}, 'prover-result':{answer:valid?'Valid':'Unknown', time:0}}));
}
process.exitCode = goals.every(name => prover === 'second' || name === 'Law_sample') ? 0 : 2;
`, { mode: 0o755 });
  const portfolio = await Why3.prove("unused.mlw", [goal, { name: "second", id: "Law_second" }],
    { binary, provers: ["first", "second"], jobs: 1 });
  check(() => assert.deepEqual(portfolio.map((r) => [r.valid, r.attempts.length]), [[true, 1], [true, 2]]));
  for (const jobs of [0, -1, 0.5, Infinity, NaN, 65]) {
    await assert.rejects(() => Why3.prove("unused.mlw", [goal], { binary, jobs }));
    checks++;
  }
  await assert.rejects(() => Why3.prove("unused.mlw", [goal, goal], { binary }), /duplicate proof obligation/);
  checks++;
}

async function parallel_tests(): Promise<void> {
  const binary = path.join(TEMP, "parallel tool"), log = path.join(TEMP, "parallel.jsonl");
  const goals = ["a", "b", "c"].map((name) => ({ name, id: "Law_" + name }));
  fs.writeFileSync(binary, `#!/usr/bin/env node
const fs = require('node:fs'), args = process.argv.slice(2);
const prover = args[args.indexOf('-P')+1], goals = args.flatMap((x,i) => x === '-G' ? [args[i+1]] : []), goal = goals.join(',');
const event = phase => fs.appendFileSync(${JSON.stringify(log)}, JSON.stringify({phase,prover,goal,pid:process.pid})+'\\n');
event('start');
setTimeout(() => {
  event('end');
  for (const name of goals) console.log(JSON.stringify({term:{goal_name:name},'prover-result':{answer:prover==='fast'?'Unknown':'Valid',time:0}}));
  process.exitCode = prover==='fast'?2:0;
}, prover==='fast'?25:100);
`, { mode: 0o755 });
  for (const jobs of [1, 2, 4]) {
    fs.writeFileSync(log, "");
    const results = await Why3.prove("unused.mlw", goals, { binary, jobs, provers: ["fast", "valid"] });
    check(() => assert.ok(results.every((r) => r.valid)));
    check(() => assert.deepEqual(results.map((r) => r.goal.id), goals.map((g) => g.id)));
    const events = fs.readFileSync(log, "utf8").trim().split("\n").map((s) => JSON.parse(s));
    const active = new Map<number, {goal: string; prover: string}>();
    let peak = 0, overlapped = false;
    for (const e of events) {
      if (e.phase === "start") active.set(e.pid, e); else active.delete(e.pid);
      peak = Math.max(peak, active.size);
      overlapped ||= new Set([...active.values()].map((a) => a.goal)).size > 1
        && new Set([...active.values()].map((a) => a.prover)).size > 1;
    }
    check(() => assert.ok(peak <= jobs, "shared process limit"));
    if (jobs === 1) check(() => assert.equal(peak, 1));
    if (jobs === 4) check(() => assert.ok(overlapped, "different goals and ATPs must overlap"));
  }

  // Cancellation must also remove queued work, without launching it later.
  fs.writeFileSync(log, "");
  fs.writeFileSync(binary, `#!/usr/bin/env node
require('node:fs').appendFileSync(${JSON.stringify(log)}, String(process.pid)+'\\n');
setInterval(() => {}, 1000);
`, { mode: 0o755 });
  const stop = new AbortController();
  const work = Why3.prove("unused.mlw", goals, { binary, jobs: 1, provers: ["one", "two"] }, stop.signal);
  const rejected = assert.rejects(work, /cancelled/);
  try {
    const deadline = Date.now() + 5000;
    while (!fs.readFileSync(log, "utf8") && Date.now() < deadline) await new Promise((r) => setTimeout(r, 10));
  } finally { stop.abort(); }
  await rejected;
  checks++;
  const pids = fs.readFileSync(log, "utf8").trim().split("\n").map(Number);
  check(() => assert.equal(pids.length, 1));
  check(() => assert.ok(pids[0] > 0));
  check(() => assert.throws(() => process.kill(pids[0], 0), (e: NodeJS.ErrnoException) => e.code === "ESRCH"));
}

async function gate(): Promise<void> {
  const available = child.spawnSync(WHY3, ["--version"], { encoding: "utf8" }).status === 0;
  if (!available && process.argv.includes("--require-prover")) throw new Error("Why3 is required for this gate");
  await fake_tests();
  await parallel_tests();
  const dir = path.join(ROOT, "tests/why3");
  for (const name of fs.readdirSync(dir).filter((n) => n.endsWith(".bend")).sort()) {
    const file = path.join(dir, name);
    const src = fs.readFileSync(file, "utf8");
    const expectation = /^# why3: (.+)$/m.exec(src)![1];
    const laws = [...src.matchAll(/^# why3-law: (.+)$/gm)].map((m) => m[1]);
    const induct = [...src.matchAll(/^# why3-induct: (.+)$/gm)].map((m) => m[1]);
    const { book, files } = await read(file);
    const normal = cli([file, "--kernel-only"]);
    const golden = src.split("\n").filter((l) => l.startsWith("#|")).map((l) => l.slice(2)).join("\n");
    const normal_output = (normal.stdout + normal.stderr).trim()
      + (normal.status === 0 ? "" : "\nexit " + normal.status);
    check(() => assert.equal(normal_output, golden, name + ": normal CLI behavior"));
    if (expectation.startsWith("Reject ")) {
      check(() => assert.throws(() => Why3.export_book(book, { files, laws, induct }),
        (e: unknown) => String(e).includes(expectation.slice(7)), name));
      continue;
    }
    const exported = Why3.export_book(book, { files, laws, induct });
    check(() => assert.ok(exported.goals.length > 0, name + ": goals must exist"));
    check(() => assert.equal(new Set(exported.goals.map((g) => g.id)).size, exported.goals.length));
    check(() => assert.ok(!/\b(?:axiom|lemma)\b/.test(exported.source), "laws must not be assumed"));
    // Re-exporting a checked book is stable, including shared type cells.
    check(() => assert.equal(Why3.export_book(book, { files, laws, induct }).source, exported.source));
    if (name === "shadow.bend") check(() => assert.ok(!exported.source.includes("BV32")));
    if (name === "imported.bend") check(() => assert.ok(exported.goals.some((g) =>
      g.name === "filled.reflexive" && g.file === path.join(dir, "filled.bend"))));
    if (available) {
      const mlw = path.join(TEMP, name + ".mlw");
      fs.writeFileSync(mlw, exported.source);
      const typed = child.spawnSync(WHY3, ["prove", "--type-only", mlw], { encoding: "utf8", timeout: 10000 });
      check(() => assert.equal(typed.status, 0, name + ": " + typed.stderr));
      const results = await Why3.prove(mlw, exported.goals, { binary: WHY3, provers: [PROVER],
        timeout: expectation === "Valid" ? 5 : 1 });
      for (const r of results) check(() => assert.equal(r.valid, expectation === "Valid",
        name + ": " + r.goal.name + " " + JSON.stringify(r.attempts)));
    }
  }
  const file = path.join(dir, "arithmetic.bend");
  const { book, files } = await read(file);
  check(() => assert.throws(() => Why3.export_book(book, { laws: ["absent"] }), /unknown law/));
  check(() => assert.throws(() => Why3.export_book(book, { laws: ["add_zero"], induct: ["absent"] }), /no quantified/));
  const selected = Why3.export_book(book, { files, laws: ["add_zero"], induct: ["n"] });
  check(() => assert.equal(selected.goals.length, 1));
  check(() => assert.ok(selected.source.includes("[@induction]")));
  const out = path.join(TEMP, "exported.mlw");
  const emitted = cli([file, "--why3", "--law", "wrap", "-o", out]);
  check(() => assert.equal(emitted.status, 0, emitted.stderr));
  check(() => assert.ok(fs.readFileSync(out, "utf8").includes("goal Law_wrap:")));
  check(() => assert.ok(cli([file, "--why3", "--law", "wrap"]).stdout.startsWith("(* Generated")));
  check(() => assert.equal(cli([file, "-o", out]).status, 0));
  for (const args of [["--timeout"], ["--why3", "--timeout", "0"], ["--prove", "--timeout", "NaN"],
    ["--jobs"], ["--prove", "--jobs", "0"], ["--why3", "--jobs", "65"], ["--prove", "--jobs", "1.5"],
    ["--why3", "--publish"], ["--why3", "--checkup"], ["--why3", "-o", "bad.js"],
    ["--law", "wrap"], ["--prove", "argument"], ["--why3", "--", "--prover"],
    ["--why3", "--kernel-only"], ["--why3", "-o", out, "-o", out], ["--prove", "--why3-bin", path.join(TEMP, "missing")]]) {
    check(() => assert.notEqual(cli([file, ...args]).status, 0, args.join(" ")));
  }
  const link = path.join(TEMP, "source.mlw");
  fs.symlinkSync(file, link);
  check(() => assert.notEqual(cli([file, "--why3", "-o", link]).status, 0));
  fs.writeFileSync(out, "keep this output");
  check(() => assert.notEqual(cli([path.join(dir, "unsafe.bend"), "--why3", "-o", out]).status, 0));
  check(() => assert.equal(fs.readFileSync(out, "utf8"), "keep this output"));
  check(() => assert.notEqual(cli([file, "--why3", "--why3-config", out, "-o", out]).status, 0));
  if (available) {
    const good = cli([file, "--prove", "--law", "wrap", "--why3-bin", WHY3, "--prover", PROVER]);
    check(() => assert.equal(good.status, 0, good.stderr));
    check(() => assert.match(good.stdout, /1\/1 laws proved by Why3/));
    const bad = cli([path.join(dir, "false.bend"), "--why3", "--prove", "--timeout", "1", "--why3-bin", WHY3, "--prover", PROVER]);
    check(() => assert.equal(bad.status, 1, bad.stderr));
    check(() => assert.match(bad.stdout, /0\/2 laws proved by Why3/));
    const main = cli([path.join(dir, "with_main.bend"), "--prove", "--why3-bin", WHY3, "--prover", PROVER]);
    check(() => assert.equal(main.status, 0, main.stderr));
    check(() => assert.ok(!main.stdout.includes("42n")));
  }
  console.log("PASS: " + checks + " checks" + (available ? " (including real Why3 proofs)" : " (Why3 proofs SKIPPED: executable unavailable)"));
}

try {
  await gate();
} finally {
  fs.rmSync(TEMP, { recursive: true, force: true });
}
