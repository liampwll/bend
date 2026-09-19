# Automatic proofs and theorem reuse

Why3 is part of normal Bend proof checking. An unfilled law is an automatic
proof obligation; `?auto` requests automation at a step inside a manual proof.
Successfully proved laws become opaque theorems that later Bend proofs can
call. Earlier verified theorems, including supported manual proofs, are also
available as hypotheses to later Why3 obligations.

Install [Why3](https://why3.org/doc/install.html) and an automated prover such
as Alt-Ergo, Z3 or [cvc5](https://github.com/cvc5/cvc5/releases), then register
the prover:

```sh
why3 config detect
why3 config list-provers
```

The default prover is the Why3 shortcut `alt-ergo`. Use `--prover z3` for Z3;
it is especially useful for bitvector arithmetic. `--prover cvc5` selects
cvc5. Why3 1.8.2 is the tested release. Programs with complete manual proofs
do not invoke Why3. Automatic proofs require Why3 and the selected prover
on the machine. From a source checkout, replace `bend` below with
`bun bend2/main.ts`. The CLI requires Bun; Node 24+ supports the import hook
and the Why3 API.

cvc5 1.4.0 changed its version banner, which Why3 1.8.2's detector does not
recognize. That combination works with an explicit entry in `why3.conf`;
replace `/path/to/cvc5` with the installed executable's absolute path:

```ini
[prover]
name = "CVC5"
version = "1.4.0"
shortcut = "cvc5"
driver = "cvc5"
command = "'/path/to/cvc5' --stats-internal --tlimit=%T %f"
```

## Automatic checking

```python
import Base

# No def needed: Why3 proves this by structural induction.
law add_zero:
  for n: Nat
  {Nat.add(n, 0n) == n : Nat}

# The automated result is an ordinary usable theorem in a full Bend proof.
def reuse(n: Nat) -> {Nat.add(n, 0n) == n : Nat}:
  add_zero(n)

# Later ATP goals can use add_zero and the checked theorem reuse.
def nested(n: Nat) -> {Nat.add(Nat.add(n, 0n), 0n) == n : Nat}:
  ?auto

# Manual reasoning and automatic steps can be mixed.
def transport(a: Nat, b: Nat, h: {a == b : Nat}) -> {Nat.add(a, 0n) == b : Nat}:
  %p@h : {Nat.add(a, 0n) == _ : Nat}
  ?auto
```

Run `bend PROOF.bend` normally. This also works for imported laws, compilation,
`--checkup`, publishing checks, Bun's loader and Node's import hook. Supplied
manual proof bodies are always checked; automation never hides an incorrect
proof. Names follow Bend's existing declaration order. A theorem cannot use
itself or a future theorem as an ATP premise.

```sh
bend PROOF.bend                               # check, then run main if present
bend PROOF.bend --prove                       # same checking, without main
bend PROOF.bend --prove -o proofs.mlw          # save successful ATP tasks
bend PROOF.bend --prover z3 --timeout 2
bend PROOF.bend --prover alt-ergo --prover z3
bend PROOF.bend --prover z3 --prover alt-ergo --jobs 8
bend PROOF.bend --prover z3 --prover alt-ergo --prover cvc5 --jobs 8
bend PROOF.bend --induct n
bend PROOF.bend --kernel-only                 # require only Bend proof terms
```

The automatic timeout is **one second per goal and prover**. Ready independent
goals are grouped into batches of up to 32, reusing one Why3 process per batch
and prover. Each goal keeps a separate input theory and its own verified
premises. Configured provers race on each batch; once every goal has a validated
answer, remaining attempts are cancelled and reaped. A losing worker can
continue work on an already solved goal while other goals in its batch remain
unproved. Definitions that reference pending proofs wait for them.
The scheduler also waits for earlier computational lemmas whose
symbols occur in the goal's dependencies, so useful facts are ready before
starting the ATPs. An unsuccessful independent attempt waits for earlier lemmas before
retrying. Local holes within one definition still elaborate in order.
Each obligation first receives earlier facts
whose symbols occur in its dependencies. If that attempt fails, it retries
with all supported earlier facts, so filtering does not discard useful lemmas.

`--jobs` limits the total number of simultaneous Why3/prover attempts per check
across all goals and ATPs, from 1 to 64. The default is the available CPU count, capped
at 16. `--jobs 1` serializes prover attempts. Pending and later claims never
become ATP assumptions, and a failed check cancels running and queued work.
Evidence is reported in source order even when proofs finish out of order.
The wrapper shares a versioned declaration context and indexes facts by their
dependencies. Each native check uses only the transitive closure of visible
dependencies, including constructor types. The unchanged Bend kernel checks
the new declaration. Context views exclude later declarations even if another
worker finishes them first. These indexes are rebuilt on each load; they are
not a persistent proof cache.
Additional ATPs can improve coverage but also compete for these process slots.
Compare full proof-checking times before expanding a portfolio; cancelled
attempts do not show whether a prover could have proved the goal.

Local `?auto` first tries without consuming local hypotheses, unless its
equality clearly needs premises (for example, distinct constructors or two
independent values). An unsuccessful attempt retries with supported live
hypotheses. This keeps easy steps from unnecessarily consuming affine proof
arguments. Local data parameters are passed erased; live evidence still
counts towards the kernel's ordinary use limits. Erased proof parameters
can never become ATP premises.

An unknown result, timeout, missing result, unsupported goal or tool failure
fails checking. Add a manual proof or raise the timeout for harder goals.
`?TODO` remains incomplete and is never used as proof evidence. A computational
signature, such as `law f: Nat -> Nat`, needs an implementation, not an ATP
validity answer. `?auto` also needs a known proof goal: annotate an inferred
local binding, for example `h = {?auto : {n == n : Nat}}`.

`--why3-bin` and `--why3-config` select an executable and configuration.
For loaders, use `BEND_WHY3`, `BEND_WHY3_PROVERS` (comma-separated shortcuts),
`BEND_WHY3_TIMEOUT`, `BEND_WHY3_JOBS`, and Why3's `WHY3CONFIG`. CLI settings take precedence.
The process reports how many obligations rely on trusted ATP evidence.
Every fresh load reproves its obligations; no disk certificate is accepted
as a shortcut after source or dependency changes.

The complete example is [PROOF.bend](../demos/proof_why3/PROOF.bend), which
imports [LAWS.bend](../demos/proof_why3/LAWS.bend). The exported proof session
contains one module per successful obligation. Its `Fact_` axioms are earlier
theorems already proved by Why3 or checked by Bend, never pending claims.

[Companions of every demo](../demos/why3/README.md) preserve the original laws
and programs and compare their manual and automated proofs. Run
`bun gates/demos.ts` to check every pair with the one-second prover budget;
`--write-report` refreshes the measurements and `--sessions .tmp/demo-sessions`
exports the successful obligations for inspection.

## Standalone exports

Write `LAWS.bend`:

```python
import Base

law add_zero:
  for n: Nat
  {Nat.add(n, 0n) == n : Nat}

law wrap:
  {U32.add(4294967295, 1) == 0 : U32}

law successor_witness:
  for n: Nat
  exs m: Nat
  {m == 1n+n : Nat}
```

Export, inspect, or prove:

```sh
bend LAWS.bend --why3                         # WhyML on stdout
bend LAWS.bend -o laws.mlw                    # same export to a file
bend LAWS.bend --why3 --prove                 # independently prove each goal
bend LAWS.bend --why3 --prove -o laws.mlw      # keep the independent task file
why3 ide laws.mlw                            # interactive proof work
```

Standalone proving reports each law at its Bend source location and exits
with status zero only when every selected law has a `Valid` result. An unknown result,
timeout, invalid goal, missing answer, translation error, or tool failure
fails the command. An unproved law is not necessarily false.

The standalone exporter selects open laws and filled laws whose result is a
proposition, including imported laws. Filled computational signatures such as `law add:
for x: Nat ... Nat` are function definitions, not proof goals. An open
computational signature is an error, not an uninterpreted assumption.
`--law <name>` selects a particular law or theorem def for independent
verification; repeat it to select several. With `--prove`, this selects the
standalone workflow instead of checking the entire mixed proof. Imported
names are canonical module paths (`math.add_zero` for
`import ./math.bend as M`), not the local alias `M.add_zero`.

```sh
bend LAWS.bend --prove --law add_zero
bend LAWS.bend --why3 --prove --prover alt-ergo --prover z3
bend LAWS.bend --why3 --prove --induct n
bend LAWS.bend --why3 --prove --why3-bin /opt/why3/bin/why3 --why3-config my-why3.conf
```

Standalone mode also batches independent goals and runs ATPs concurrently,
sharing the `--jobs` limit. A batch stops its remaining attempts after every
goal has a validated proof. `--timeout` is a positive integer number of seconds
per law, per prover, with a default of five in standalone mode. Why3's
`induction_ty_lex` transformation looks for structural induction candidates;
`--induct` marks a named quantified variable explicitly. For proofs needing
additional lemmas, case splits, or a different strategy, keep the `.mlw`
file and use Why3's IDE. Each export is self-contained and deterministic.
Standalone exports contain independent goals and no assumed laws; they do
not elaborate `?auto` or admit open-law references inside manual proofs.
Use normal checking and `--prove -o proofs.mlw` for those mixed proofs.

## Specifications

Equality, universal quantification, implication, conjunction (`&`),
disjunction (`|`), negation (`!=`), and existential witnesses (`exs`) are
supported. `Empty` is false and Base's `Unit` is true. Preconditions are
ordinary live proof parameters or implication domains:

```python
law increment_zero:
  for n: Nat
  for precondition: {n == 0n : Nat}
  {Nat.add(n, 1n) == 1n : Nat}
```

Postconditions can refer to a function result using a local binding:

```python
law append_length:
  for xs: List<Nat>
  for ys: List<Nat>
  result = List.append(&1, Nat, xs, ys)
  {List.length(&1, Nat, result) == Nat.add(List.length(&1, Nat, xs), List.length(&1, Nat, ys)) : Nat}
```

The actual function bodies are translated, so changing their implementation
changes the proof obligations. In integrated checking only verified earlier
facts become assumptions. In standalone exports every selected law is an
independent goal, even when a Bend proof body exists.

## Supported programs and trust

The backend supports a first-order subset: concrete positive algebraic data
types, pattern matching, constructors, local bindings, fully applied pure
functions, and structural recursion accepted by Why3. Type and quantity
parameters are specialized at their concrete call sites, so collections such
as `List<Nat>`, `List<U32>`, products, and user-defined trees can be exported.
Natural numbers remain the exact `Zero`/`Succ` datatype, not bounded machine
integers. Functions over them are translated from their Bend definitions.

Closed constructor arguments are also specialized. For example, a recursive
comparison with `11n` becomes a finite case distinction, and indexing a fixed
rendered board can use its computed string. This is bounded, memoized partial
evaluation of the audited Bend definitions; it adds no assumed arithmetic or
game-specific facts. Unchanged recursive operands stay generic for theorem reuse.
Changing recursive operands must shrink, otherwise the exporter uses a generic
function; exhausted evaluation budgets also fall back to generic translation.
The [sealed-room game proof](../demos/why3_app_win_is_bug_2d/PROOF.bend) uses
this to prove a safety invariant and both original laws in 29 code lines.

Base's U32 uses Why3's `bv.BV32` theory. The mapped operations are `inc`,
`add`, `sub`, `mul`, `not`, `and`, `or`, `xor`, `shl`, `shr`, `div`, `mod`,
and the six equality/order comparisons. Arithmetic wraps at 32 bits, shifts
are logical one-bit shifts, `x / 0` is zero, and `x % 0` is `x`, matching
Base. Other U32 helpers can be translated from their bodies when they stay
inside the supported subset. U32 constants are exported as typed bitvector
literals, such as `(4294967295 : BV32.t)`, avoiding integer-conversion axioms.
Direct matching or construction of its `Word` representation is not supported. Mapping applies only
to definitions loaded from Base, not user functions with the same names.

Unsupported constructs cause explicit errors. These include F32, arrays,
effects and foreign calls, reachable `@unsafe` definitions, higher-order
arguments or results, value-indexed types, negative or uninhabited data
types, erased computational value/proof parameters or fields, computation
depending on proof values, and proof rewrites in computational dependencies.
Erased logical data quantifiers are supported, but erased proof hypotheses
are rejected. Unrelated functions are type-checked by Bend but do not need
to be translated. The backend does not perform flow analysis, mutable-state
verification, loop-invariant inference, or automatic counterexample reconstruction.

A Why3 result verifies the classical first-order interpretation of a law over
finite, total data values; existential results do not extract witnesses.
This is a **trusted extension of Bend's proof system**, not proof-term
reconstruction. The trusted components now include the elaborator, translation,
Base U32 mapping, Why3 and its theories, and the selected prover. The protected
`bend2/bend.ts` kernel is unchanged: the elaborator installs a proved theorem
using its existing opaque native-definition interface, then the kernel checks
every subsequent proof and use of that theorem. An entire check must succeed
before the resulting book is returned. Unchecked or unsafe manual proofs are
never exported as assumptions.

All supported logical results, including existentials and disjunctions, can
be referenced in Bend proofs. They remain opaque during checking. A validity
answer does not provide an executable existential witness or disjunction tag;
trying to execute such evidence fails explicitly. Supply a Bend body when you
need to compute that data. For a constructive existential, return `(witness,
?auto)` so the ATP proves the property of the witness you supplied.

Equality evidence is erased only in a separate runtime view, just as the
compiler already erases equality elimination. That runtime representation
is never checked as if it were a reconstructed proof. `--kernel-only` disables
the extension and preserves the original requirement for complete Bend proof
terms. `--prove` never runs `main` or publishes anything.

## Implementation and tests

`bend2/why3.ts` implements translation, ordered proof elaboration, theorem
provenance, runtime erasure and prover invocation; `bend2/main.ts` integrates
it into loading and checking. `evidence(book)` exposes each successful task,
its source, SHA-256 digest, assumptions and prover answers.

The Why3 gates are local and need no mini cluster:

```sh
WHY3_PROVER=z3 bun gates/why3.ts --require-prover
WHY3_PROVER=z3 bun gates/auto.ts --require-prover
# Node 24+ can also run both gates; Bun must be on PATH or set with BUN.
```

`WHY3` overrides the test executable and `WHY3CONFIG` is Why3's standard
configuration override. Use a prover with bitvector support for the full
suite. Without `--require-prover`, the gate still tests translation, CLI
compatibility, and failure handling when Why3 is unavailable, and explicitly
reports skipped real proofs. The tests include true and false laws, induction,
monomorphization, imports, numeric edge cases, and malformed, missing,
duplicated, or unsuccessful prover responses. The integration gate checks
theorem reuse, local affine hypotheses, imports, execution, compilation,
loaders, stale source changes and the opacity of executable witnesses.
The cluster gate runs kernel/runtime fixtures with `--kernel-only`; automatic
proof fixtures in `tests/auto` run in `gates/auto.ts` with actual provers.
