# pure_par_sort: Why3 companion

Why3 proves the arithmetic and Boolean helper lemmas. The manual inductions on indexed trees call those theorems.

[Original proof](../pure_par_sort/PROOF.bend) · [Companion proof](PROOF.bend) · [All comparisons](../why3/README.md)

Proof file: **91 → 56 code lines** (38.5% reduction); **3567 → 2663 code bytes**. 6 ATP obligations checked; 5 include earlier verified facts.

Every original specification, program and asset is copied byte for byte. Counts exclude blank lines and full-line comments, include imports and helper definitions, and exclude this documentation.

From the repository root, after registering Z3 and Alt-Ergo with Why3:

```sh
bun bend2/main.ts demos/why3_pure_par_sort/PROOF.bend --prove --prover z3 --prover alt-ergo --timeout 1
```

These commands check proofs without running main. See the [integration guide](../../guide/WHY3.md) for setup, export commands and the trusted ATP boundary.
