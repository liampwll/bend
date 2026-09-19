# pure_par_sum: Why3 companion

Four automated lemmas replace the explicit inductions and rewrites. Earlier arithmetic facts are available to the sequence and tree proofs.

[Original proof](../pure_par_sum/PROOF.bend) · [Companion proof](PROOF.bend) · [All comparisons](../why3/README.md)

Proof file: **35 → 12 code lines** (65.7% reduction); **1630 → 416 code bytes**. 4 ATP obligations checked; 3 include earlier verified facts.

Every original specification, program and asset is copied byte for byte. Counts exclude blank lines and full-line comments, include imports and helper definitions, and exclude this documentation.

From the repository root, after registering Z3 and Alt-Ergo with Why3:

```sh
bun bend2/main.ts demos/why3_pure_par_sum/PROOF.bend --prove --prover z3 --prover alt-ergo --timeout 1 --induct a --induct n
```

These commands check proofs without running main. See the [integration guide](../../guide/WHY3.md) for setup, export commands and the trusted ATP boundary.
