# proof_numerics: Why3 companion

Why3 proves addition and multiplication lemmas, discharges contradictory comparison cases, and uses checked le_eq in wrap_eq. Division retains explicit witnesses and induction.

[Original proof](../proof_numerics/PROOF.bend) · [Companion proof](PROOF.bend) · [All comparisons](../why3/README.md)

Proof file: **119 → 57 code lines** (52.1% reduction); **4046 → 2136 code bytes**. 13 ATP obligations checked; 11 include earlier verified facts.

Every original specification, program and asset is copied byte for byte. Counts exclude blank lines and full-line comments, include imports and helper definitions, and exclude this documentation.

From the repository root, after registering Z3 and Alt-Ergo with Why3:

```sh
bun bend2/main.ts demos/why3_proof_numerics/PROOF.bend --prove --prover z3 --prover alt-ergo --timeout 1
```

These commands check proofs without running main. See the [integration guide](../../guide/WHY3.md) for setup, export commands and the trusted ATP boundary.
