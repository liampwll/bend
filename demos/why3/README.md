# Why3 companions for every demo

Each `demos/why3_<name>/` directory is a complete companion of the original
demo. Its `LAWS.bend`, executable sources and assets are identical to the
originals. Only `PROOF.bend` changes. Each companion has a `WHY3.md` with its
comparison, remaining manual work and exact checking command.

The automatic proofs use the core proof workflow: open laws are discharged
when declared, and `?auto` closes local obligations using earlier verified
theorems. Full Bend proofs can then call these results. The comparisons retain
manual proofs when translation is unsupported or provers do not finish within
the short timeout. An unchanged demo is reported as such. The netcode demo has
no original proof file; `proof_why3` was already automated.

## Measured results

Counts cover **all nonblank, non-comment lines of `PROOF.bend`**, including
imports, theorem statements and helper definitions. Line wrapping and indentation
are preserved except where a proof is rewritten. Removing comments cannot improve
the result. Original specification files are excluded equally on both sides.

<!-- comparison:start -->
| Demo | Original lines | Why3 lines | Reduction | ATP goals |
| --- | ---: | ---: | ---: | ---: |
| [app_pong_game_2d](../why3_app_pong_game_2d/WHY3.md) | 52 | 5 | 90.4% | 1 |
| [app_ray_tracer_3d](../why3_app_ray_tracer_3d/WHY3.md) | 15 | 10 | 33.3% | 1 |
| [app_slash_boss_3d](../why3_app_slash_boss_3d/WHY3.md) | 86 | 77 | 10.5% | 1 |
| [app_triangle_2d](../why3_app_triangle_2d/WHY3.md) | 12 | 12 | 0.0% | 0 |
| [app_win_is_bug_2d](../why3_app_win_is_bug_2d/WHY3.md) | 391 | 29 | 92.6% | 4 |
| [io_hello_world](../why3_io_hello_world/WHY3.md) | 5 | 5 | 0.0% | 0 |
| [io_http_fetch](../why3_io_http_fetch/WHY3.md) | 26 | 26 | 0.0% | 1 |
| [io_http_server](../why3_io_http_server/WHY3.md) | 17 | 5 | 70.6% | 1 |
| [io_rollback_netcode](../why3_io_rollback_netcode/WHY3.md) | — | — | n/a | 0 |
| [io_tcp_echos](../why3_io_tcp_echos/WHY3.md) | 7 | 3 | 57.1% | 2 |
| [proof_insertion_sort](../why3_proof_insertion_sort/WHY3.md) | 56 | 48 | 14.3% | 1 |
| [proof_numerics](../why3_proof_numerics/WHY3.md) | 119 | 57 | 52.1% | 13 |
| [proof_typed_eval](../why3_proof_typed_eval/WHY3.md) | 40 | 40 | 0.0% | 0 |
| [proof_why3](../why3_proof_why3/WHY3.md) | 18 | 18 | 0.0% | 6 |
| [pure_hvm5_mini](../why3_pure_hvm5_mini/WHY3.md) | 157 | 117 | 25.5% | 7 |
| [pure_par_sort](../why3_pure_par_sort/WHY3.md) | 91 | 56 | 38.5% | 6 |
| [pure_par_sum](../why3_pure_par_sum/WHY3.md) | 35 | 12 | 65.7% | 4 |
| **Total** | **1127** | **520** | **53.9%** | **48** |

Proof source bytes: **41054 → 19304** (53.0% smaller), using the same comment/blank-line filter.

Validated **17/17 demo pairs**, covering **20 entrypoints** in each set, with `z3, alt-ergo` and a **one-second limit per goal and prover**.
<!-- comparison:end -->

## Read the proofs

- [Winning Is Impossible](../why3_app_win_is_bug_2d/PROOF.bend): a safety
  invariant replaces the finite-map certificate. Why3 proves preservation by
  one step and by a move list, plus the two observations of a safe state.
  The final Bend proofs apply those theorems. Bounds are explicit because the
  original game uses unrestricted naturals; the rendered-flag law still checks
  the actual string returned by `grid`.
- [Pong](../why3_app_pong_game_2d/PROOF.bend): an imported law replaces a
  16-case helper and its application. Esc still uses ordinary reflexivity.
- [Parallel sum](../why3_pure_par_sum/PROOF.bend): automatic arithmetic facts
  support the sequence lemma and then the tree theorem.
- [Numerics](../why3_proof_numerics/PROOF.bend): automated lemmas support a
  manual division proof with explicit quotient and remainder witnesses.
- [Parallel sort](../why3_pure_par_sort/PROOF.bend): manual induction on
  dependent trees uses arithmetic theorems proved by Why3.

For example, the parallel sort helper originally contained an induction:

```python
def add_zero(a: Nat) -> {a == Nat.add(a, 0n) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_zero(p) : {1n+p == 1n+_ : Nat}
      {==}
```

The companion keeps its type and lets Why3 prove it:

```python
def add_zero(a: Nat) -> {a == Nat.add(a, 0n) : Nat}:
  ?auto
```

Later obligations can use this theorem automatically. The larger tree proofs
still use Bend's dependent types and induction.

## Reproduce and export

Install Why3, Z3 and Alt-Ergo, then run `why3 config detect`. See the
[integration guide](../../guide/WHY3.md) for configuration and trust details.
From the repository root:

```sh
bun gates/demos.ts
bun gates/demos.ts --write-report
bun gates/demos.ts --sessions .tmp/demo-sessions
```

Node 24+ also runs the gate. `WHY3` selects the Why3 executable;
`WHY3CONFIG` selects its configuration; `WHY3_PROVERS` overrides the default
`z3,alt-ergo` portfolio. The limit stays at one second per goal and prover.
Local automation may first try without hypotheses and then with live hypotheses.
Induction hints for individual demos are recorded in their `WHY3.md` files and
applied by the gate. The gate checks the originals as well as the companions,
asserts that all specifications and executable sources are identical, and never
runs GUI, network or other `main` effects. It updates measurements only after
every pair checks successfully.

The gate also tests two broken versions of the sealed-room game in temporary
directories: opening the north wall must invalidate step preservation, and
drawing a flag on the safe start cell must invalidate the rendered-flag claim.

The session files contain the actual accepted WhyML obligations and the earlier
verified facts used as premises. They are proof records, not executable witness
programs. ATP results remain a trusted extension; no reconstructed Bend proof
terms or solver-independent certificates are claimed.
