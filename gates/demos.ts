#!/usr/bin/env bun
// Check every original/Why3 demo pair, preserve the specifications and program
// files byte for byte, and measure proof source after both books have checked.
import * as assert from "node:assert/strict";
import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import * as Bend from "../bend2/bend.ts";
import * as Why3 from "../bend2/why3.ts";

const ROOT = path.resolve(import.meta.dirname, "..");
const DEMOS = path.join(ROOT, "demos");
const PROVERS = (process.env.WHY3_PROVERS ?? "z3,alt-ergo").split(",").filter(Boolean);
const args = process.argv.slice(2);
const write = args.includes("--write-report");
const sessionArg = args.indexOf("--sessions");
const sessions = sessionArg < 0 ? undefined : args[sessionArg + 1];
assert.ok(sessionArg < 0 || sessions && !sessions.startsWith("--"), "--sessions needs a directory");
for (let i = 0; i < args.length; i++) {
  if (args[i] === "--sessions") { i++; continue; }
  assert.equal(args[i], "--write-report", "unknown argument: " + args[i]);
}

type Note = { text: string; induct?: string[] };
const NOTES: Record<string, Note> = {
  app_pong_game_2d: { text: "The imported last-press law is automatic; the four-slot helper and its 16 Boolean cases disappear. Esc still checks by computation." },
  app_ray_tracer_3d: { text: "A general set/get lemma is automatic. Put the index first so induction generalizes the held-key list, then reuse that lemma in the original law. Esc still checks by computation.", induct: ["k"] },
  app_slash_boss_3d: { text: "Why3 proves toggle_twice from its Boolean and U32 premises. The proofs about the full game state retain their manual steps because F32 is outside the exporter." },
  app_triangle_2d: { text: "Unchanged: the short click proofs use a coordinate conversion that matches U32's Word representation, which the exporter rejects." },
  app_win_is_bug_2d: { text: "One bounded safety invariant replaces the finite-map certificate and its Boolean proof kit. Why3 proves that safety implies both observations, that a step preserves safety, and that any move list preserves it. The final proofs apply these theorems. The rendered-flag claim still indexes the actual grid string; neither law nor the game is changed." },
  io_hello_world: { text: "Unchanged: the original is one reflexivity proof of an IO expression. IO is outside the exporter." },
  io_http_fetch: { text: "The suffix law uses the previously checked constructive suffix lemma through Why3. The string-walking induction remains manual; this does not reduce the proof's line count." },
  io_http_server: { text: "Why3 proves response injectivity automatically, removing the auxiliary drop function. The header witness remains an explicit Bend value." },
  io_rollback_netcode: { text: "No proof file or laws in the original, so there is no proof-size baseline. All four Bend modules are copied and checked without running the networked program." },
  io_tcp_echos: { text: "Both imported laws are automatic. The proof file only needs its imports." },
  proof_insertion_sort: { text: "Why3 replaces bump_swap's four Boolean cases. The dependent sortedness and permutation arguments retain their manual proofs." },
  proof_numerics: { text: "Why3 proves addition and multiplication lemmas, discharges contradictory comparison cases, and uses checked le_eq in wrap_eq. Division retains explicit witnesses and induction." },
  proof_typed_eval: { text: "Unchanged: these proofs operate on value-indexed expressions and computational proof rewrites, which the exporter rejects." },
  proof_why3: { text: "Already automatic in the original. This copy preserves the existing example, including local automation, theorem reuse and opaque existential evidence." },
  pure_hvm5_mini: { text: "Automatic lexer and printer lemmas feed the remaining manual proofs. The interpreter's existing unsafe definitions are unchanged; Why3 does not admit them as premises." },
  pure_par_sort: { text: "Why3 proves the arithmetic and Boolean helper lemmas. The manual inductions on indexed trees call those theorems." },
  pure_par_sum: { text: "Four automated lemmas replace the explicit inductions and rewrites. Earlier arithmetic facts are available to the sequence and tree proofs.", induct: ["a", "n"] },
};

function files(dir: string, prefix = ""): string[] {
  return fs.readdirSync(dir, { withFileTypes: true }).sort((a, b) => a.name.localeCompare(b.name))
    .flatMap((f) => f.isDirectory() ? files(path.join(dir, f.name), prefix + f.name + "/") : [prefix + f.name]);
}
function code(file: string): { lines: number; bytes: number } {
  if (!fs.existsSync(file)) return { lines: 0, bytes: 0 };
  const lines = fs.readFileSync(file, "utf8").split(/\r?\n/)
    .filter((s) => s.trim() !== "" && !s.trimStart().startsWith("#"));
  return { lines: lines.length, bytes: Buffer.byteLength(lines.join("\n") + "\n") };
}
function percent(before: number, after: number): string {
  return before === 0 ? "n/a" : ((before - after) * 100 / before).toFixed(1) + "%";
}
async function check(file: string, kernelOnly: boolean, induct: string[] = []) {
  const book = Bend.book_nil();
  const loaded = new Map<string, string | null>();
  await Bend.book_load(book, file, "", loaded);
  await Why3.check_book(book, { files: loaded, kernelOnly, binary: process.env.WHY3,
    provers: PROVERS, timeout: 1, induct });
  return book;
}

async function reject_broken_game(): Promise<void> {
  const source = path.join(DEMOS, "why3_app_win_is_bug_2d");
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), "bend-game-proof-"));
  try {
    for (const file of ["main.bend", "LAWS.bend", "PROOF.bend"]) {
      fs.copyFileSync(path.join(source, file), path.join(dir, file));
    }
    const program = path.join(dir, "main.bend");
    const original = fs.readFileSync(program, "utf8");
    const proof = path.join(dir, "PROOF.bend");
    const rejects = async (pattern: RegExp) => assert.rejects(() => check(proof, false), (e: unknown) => {
      const message = (e as Bend.Err)?.$ === "Err" ? Bend.err_show(e as Bend.Err) : String(e);
      assert.match(message, pattern);
      return true;
    });
    // Opening the north wall permits a wrapped step into the sealed room.
    const opened = original.replace("north = nat_le(x, room_w()) && nat_eq(y, Nat.sub(map_h(), 1n))", "north = {False{} : Bool}");
    assert.notEqual(opened, original);
    fs.writeFileSync(program, opened);
    await rejects(/could not prove step_safe/);
    // Draw a flag on a safe cell without changing the logical on_flag test.
    // This must fail the law about the actual rendered string.
    const wrongDrawing = original.replace('pick(String, is_start, "P", ".")', 'pick(String, is_start, "F", ".")');
    assert.notEqual(wrongDrawing, original);
    fs.writeFileSync(program, wrongDrawing);
    await rejects(/could not prove safe_not_flag/);
    console.log("PASS game counterexamples: open wall and incorrect rendered flag rejected");
  } finally {
    fs.rmSync(dir, { recursive: true, force: true });
  }
}

async function main(): Promise<void> {
  const names = fs.readdirSync(DEMOS, { withFileTypes: true })
    .filter((d) => d.isDirectory() && !d.name.startsWith("why3") && files(path.join(DEMOS, d.name)).some((f) => f.endsWith(".bend")))
    .map((d) => d.name).sort();
  assert.deepEqual(Object.keys(NOTES).sort(), names, "Add a comparison note for every demo");
  const copies = fs.readdirSync(DEMOS).filter((n) => n.startsWith("why3_")).sort();
  assert.deepEqual(copies, names.map((n) => "why3_" + n), "Each demo must have exactly one companion");
  const results = [];
  let entries = 0;
  for (const name of names) {
    const original = path.join(DEMOS, name);
    const copy = path.join(DEMOS, "why3_" + name);
    const sourceFiles = files(original);
    const copyFiles = files(copy).filter((f) => f !== "WHY3.md");
    assert.deepEqual(copyFiles, sourceFiles, name + ": missing or extra program files");
    for (const file of sourceFiles) {
      if (file !== "PROOF.bend") assert.deepEqual(fs.readFileSync(path.join(copy, file)),
        fs.readFileSync(path.join(original, file)), name + ": changed specification or program: " + file);
    }
    const before = code(path.join(original, "PROOF.bend"));
    const after = code(path.join(copy, "PROOF.bend"));
    const entrypoints = sourceFiles.includes("PROOF.bend") ? ["PROOF.bend"] : sourceFiles.filter((f) => f.endsWith(".bend"));
    let automatic = 0;
    let reusing = 0;
    for (const entry of entrypoints) {
      await check(path.join(original, entry), name !== "proof_why3");
      const book = await check(path.join(copy, entry), false, NOTES[name].induct);
      const evidence = Why3.evidence(book);
      automatic += evidence.length;
      reusing += evidence.filter((e) => e.assumptions.length > 0).length;
      if (sessions !== undefined) {
        fs.mkdirSync(sessions, { recursive: true });
        fs.writeFileSync(path.join(sessions, name + "_" + path.basename(entry, ".bend") + ".mlw"), Why3.export_session(book));
      }
      entries++;
    }
    // No new unchecked escape hatches are permitted in the shortened proofs.
    if (before.lines > 0) assert.ok(!/@unsafe|\?TODO/.test(fs.readFileSync(path.join(copy, "PROOF.bend"), "utf8")), name);
    results.push({ name, before, after, automatic, reusing });
    console.log("PASS " + name + ": " + before.lines + " -> " + after.lines
      + " code lines; " + automatic + " ATP obligations, " + reusing + " with earlier facts");
  }

  await reject_broken_game();
  const total = results.reduce((a, r) => ({ before: a.before + r.before.lines,
    after: a.after + r.after.lines, bytesBefore: a.bytesBefore + r.before.bytes,
    bytesAfter: a.bytesAfter + r.after.bytes, automatic: a.automatic + r.automatic }),
  { before: 0, after: 0, bytesBefore: 0, bytesAfter: 0, automatic: 0 });
  const rows = results.map((r) => "| [" + r.name + "](../why3_" + r.name + "/WHY3.md) | "
    + (r.before.lines || "—") + " | " + (r.after.lines || "—") + " | "
    + percent(r.before.lines, r.after.lines) + " | " + r.automatic + " |");
  const report = "| Demo | Original lines | Why3 lines | Reduction | ATP goals |\n"
    + "| --- | ---: | ---: | ---: | ---: |\n" + rows.join("\n") + "\n"
    + "| **Total** | **" + total.before + "** | **" + total.after + "** | **"
    + percent(total.before, total.after) + "** | **" + total.automatic + "** |\n\n"
    + "Proof source bytes: **" + total.bytesBefore + " → " + total.bytesAfter + "** ("
    + percent(total.bytesBefore, total.bytesAfter) + " smaller), using the same comment/blank-line filter.\n\n"
    + "Validated **" + names.length + "/" + names.length + " demo pairs**, covering **" + entries
    + " entrypoints** in each set, with `" + PROVERS.join(", ") + "` and a **one-second limit per goal and prover**.\n";
  if (write) {
    const index = path.join(DEMOS, "why3/README.md");
    const text = fs.readFileSync(index, "utf8");
    assert.ok(text.includes("<!-- comparison:start -->") && text.includes("<!-- comparison:end -->"));
    fs.writeFileSync(index, text.replace(/<!-- comparison:start -->[\s\S]*?<!-- comparison:end -->/,
      "<!-- comparison:start -->\n" + report + "<!-- comparison:end -->"));
    for (const r of results) {
      const note = NOTES[r.name];
      const original = "../" + r.name + "/";
      const proof = r.before.lines > 0;
      const flag = (note.induct ?? []).map((n) => " --induct " + n).join("");
      const commands = (proof ? ["PROOF.bend"] : ["netcode.bend", "server.bend", "walkers_demo.bend", "walkers_test.bend"])
        .map((f) => "bun bend2/main.ts demos/why3_" + r.name + "/" + f
          + " --prove --prover z3 --prover alt-ergo --timeout 1" + flag).join("\n");
      fs.writeFileSync(path.join(DEMOS, "why3_" + r.name, "WHY3.md"), "# " + r.name + ": Why3 companion\n\n"
        + note.text + "\n\n"
        + (proof ? "[Original proof](" + original + "PROOF.bend) · [Companion proof](PROOF.bend) · " : "[Original demo](" + original + "README.md) · ")
        + "[All comparisons](../why3/README.md)\n\n"
        + (proof ? "Proof file: **" + r.before.lines + " → " + r.after.lines + " code lines** ("
          + percent(r.before.lines, r.after.lines) + " reduction); **" + r.before.bytes + " → " + r.after.bytes
          + " code bytes**. " : "No original proof file. ")
        + r.automatic + " ATP obligations checked; " + r.reusing + " include earlier verified facts.\n\n"
        + "Every original specification, program and asset is copied byte for byte. Counts exclude blank lines and full-line comments, include imports and helper definitions, and exclude this documentation.\n\n"
        + "From the repository root, after registering Z3 and Alt-Ergo with Why3:\n\n```sh\n" + commands + "\n```\n\n"
        + "These commands check proofs without running main. See the [integration guide](../../guide/WHY3.md) for setup, export commands and the trusted ATP boundary.\n");
    }
  }
  console.log("\n" + report);
}

main().catch((e) => {
  console.error(e?.$ === "Err" ? Bend.err_show(e) : e instanceof Error ? e.message : String(e));
  process.exitCode = 1;
});
