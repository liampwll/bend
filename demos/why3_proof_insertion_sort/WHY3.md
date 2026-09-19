# proof_insertion_sort: Why3 companion

Why3 replaces bump_swap's four Boolean cases. The dependent sortedness and permutation arguments retain their manual proofs.

[Original proof](../proof_insertion_sort/PROOF.bend) · [Companion proof](PROOF.bend) · [All comparisons](../why3/README.md)

Proof file: **56 → 48 code lines** (14.3% reduction); **2321 → 2172 code bytes**. 1 ATP obligations checked; 0 include earlier verified facts.

Every original specification, program and asset is copied byte for byte. Counts exclude blank lines and full-line comments, include imports and helper definitions, and exclude this documentation.

From the repository root, after registering Z3 and Alt-Ergo with Why3:

```sh
bun bend2/main.ts demos/why3_proof_insertion_sort/PROOF.bend --prove --prover z3 --prover alt-ergo --timeout 1
```

These commands check proofs without running main. See the [integration guide](../../guide/WHY3.md) for setup, export commands and the trusted ATP boundary.
