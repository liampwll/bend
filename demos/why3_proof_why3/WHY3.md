# proof_why3: Why3 companion

Already automatic in the original. This copy preserves the existing example, including local automation, theorem reuse and opaque existential evidence.

[Original proof](../proof_why3/PROOF.bend) · [Companion proof](PROOF.bend) · [All comparisons](../why3/README.md)

Proof file: **18 → 18 code lines** (0.0% reduction); **487 → 487 code bytes**. 6 ATP obligations checked; 3 include earlier verified facts.

Every original specification, program and asset is copied byte for byte. Counts exclude blank lines and full-line comments, include imports and helper definitions, and exclude this documentation.

From the repository root, after registering Z3 and Alt-Ergo with Why3:

```sh
bun bend2/main.ts demos/why3_proof_why3/PROOF.bend --prove --prover z3 --prover alt-ergo --timeout 1
```

These commands check proofs without running main. See the [integration guide](../../guide/WHY3.md) for setup, export commands and the trusted ATP boundary.
