# app_triangle_2d: Why3 companion

Unchanged: the short click proofs use a coordinate conversion that matches U32's Word representation, which the exporter rejects.

[Original proof](../app_triangle_2d/PROOF.bend) · [Companion proof](PROOF.bend) · [All comparisons](../why3/README.md)

Proof file: **12 → 12 code lines** (0.0% reduction); **374 → 374 code bytes**. 0 ATP obligations checked; 0 include earlier verified facts.

Every original specification, program and asset is copied byte for byte. Counts exclude blank lines and full-line comments, include imports and helper definitions, and exclude this documentation.

From the repository root, after registering Z3 and Alt-Ergo with Why3:

```sh
bun bend2/main.ts demos/why3_app_triangle_2d/PROOF.bend --prove --prover z3 --prover alt-ergo --timeout 1
```

These commands check proofs without running main. See the [integration guide](../../guide/WHY3.md) for setup, export commands and the trusted ATP boundary.
