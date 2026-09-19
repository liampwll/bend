# Why3 counterpart of proofs_3200

`why3.bend` preserves every type, law statement and computational definition
from `main.bend`. It removes 8,537 explicit theorem definitions: addition
identities and commutativity, list append identities and associativity, append
length, double mirror, and preservation of tree size under mirror. The unfilled
laws invoke Why3 during ordinary Bend checking. The generic congruence proofs
and the constructive copying functions remain checked Bend definitions.

Why3 performs structural induction and can use previously verified lemmas.
For example, tree-size preservation uses the automatically proved addition
commutativity theorem. The induction variables must be selected explicitly:

```sh
bun bend2/main.ts bench/checker/proofs_3200/why3.bend \
  --prover z3 --prover alt-ergo --timeout 1 --jobs 16 \
  --induct a --induct xs --induct t
```

The timeout is one second per ATP attempt, with sixteen shared process slots.
This does not limit the elapsed time for the entire collection of 8,537 laws.

## Reproducing the Bend-only comparison

Install Why3 and register Z3 and Alt-Ergo, then set `WHY3CONFIG` to the resulting
configuration. Run from the repository root:

```sh
WHY3CONFIG=/absolute/path/to/why3.conf \
  bun bench/checker/proofs_3200/compare.ts --repeats 3 --jobs 16
```

`BEND_WHY3` optionally selects the Why3 executable. `--provers z3,alt-ergo`
selects the portfolio; `--out <directory>` selects the results directory.
`--jobs` selects the shared process limit, defaulting to the available CPU
count capped at 16, matching ordinary checking.
Higher `--repeats` values alternate the order of the two versions and report
their medians. The default is one full check of each version.

The runner verifies that the Why3 source differs only by removal of the
selected theorem definitions. It runs the original and Why3 versions
sequentially through the same Bend CLI and checks both the exit status and
expected ATP obligation count. Timings include process startup, parsing,
native checking, translation, prover startup and proof search as applicable.
The original uses normal checking, including the integration's scan for
automation requests.

Every sample gets a fresh CLI process and temporary/configuration/cache
directories. Bun's disk transpiler cache and telemetry are disabled. No saved
proofs or Why3 sessions are reused. Normal memoization within a process and
the operating system's file cache remain enabled. Logs, commands, tool
versions, source hashes, raw times and a Markdown table are saved under
`.tmp/checker-proofs-*` by default.

Regenerate the counterpart after reviewing changes to the original:

```sh
bun bench/checker/proofs_3200/compare.ts --write-source
```

The existing cluster performance gate continues to run `main.bend`. This
comparison is opt-in and does not run the other language implementations.

## Measurements

Source size is 200,635 nonblank, noncomment lines in the original and 135,542
in the Why3 version, a reduction of 65,093 lines (32.4%). The statements and
computational code account for most of the remaining source.

On an AMD Ryzen 9 5900X Linux host exposing 16 CPUs, using Bun 1.3.10,
Why3 1.8.2, Z3 4.13.3 and Alt-Ergo 2.6.3, the median of three fresh full
checks gave:

| Version | Source lines | ATP goals | Full check (s) |
| --- | ---: | ---: | ---: |
| Original explicit proofs | 200,635 | 0 | 2.342 |
| Why3, 16 process slots | 135,542 | 8,537 | 51.554 |

The Why3 samples were 51.554, 50.769 and 51.944 seconds; every run proved
all 8,537 goals in under a minute. Original samples were 2.331, 2.381 and
2.342 seconds. A separate eight-slot run took 71.502 seconds and also proved
every goal. All used the fresh-process policy described above.
The original supplied proofs remain much faster to check than discovering
proofs through ATPs.

The integration now shares versioned declaration contexts and fact indexes,
checks each declaration against its transitive dependencies, and indexes
source line positions once. Ready goals accumulate while workers are busy,
then run in batches of up to 32 through each Why3 process. Each goal retains
its own theory and verified premises; the two ATPs race on each batch within
the shared process limit. These changes avoid repeated prefix construction,
source rescanning and most Why3 startup costs. The Bend kernel is unchanged.

Before these optimizations, the initial run was interrupted after 581.5
seconds with 4,300 of 8,537 goals started. It supplies no complete baseline
time, so no exact full-run speedup is claimed.
