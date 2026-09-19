# proof_typed_eval: Why3 companion

Unchanged: these proofs operate on value-indexed expressions and computational proof rewrites, which the exporter rejects.

[Original proof](../proof_typed_eval/PROOF.bend) · [Companion proof](PROOF.bend) · [All comparisons](../why3/README.md)

Proof file: **40 → 40 code lines** (0.0% reduction); **2341 → 2341 code bytes**. 0 ATP obligations checked; 0 include earlier verified facts.

Every original specification, program and asset is copied byte for byte. Counts exclude blank lines and full-line comments, include imports and helper definitions, and exclude this documentation.

From the repository root, after registering Z3 and Alt-Ergo with Why3:

```sh
bun bend2/main.ts demos/why3_proof_typed_eval/PROOF.bend --prove --prover z3 --prover alt-ergo --timeout 1
```

These commands check proofs without running main. See the [integration guide](../../guide/WHY3.md) for setup, export commands and the trusted ATP boundary.
