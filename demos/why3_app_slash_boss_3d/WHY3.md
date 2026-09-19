# app_slash_boss_3d: Why3 companion

Why3 proves toggle_twice from its Boolean and U32 premises. The proofs about the full game state retain their manual steps because F32 is outside the exporter.

[Original proof](../app_slash_boss_3d/PROOF.bend) · [Companion proof](PROOF.bend) · [All comparisons](../why3/README.md)

Proof file: **86 → 77 code lines** (10.5% reduction); **2979 → 2644 code bytes**. 1 ATP obligations checked; 0 include earlier verified facts.

Every original specification, program and asset is copied byte for byte. Counts exclude blank lines and full-line comments, include imports and helper definitions, and exclude this documentation.

From the repository root, after registering Z3 and Alt-Ergo with Why3:

```sh
bun bend2/main.ts demos/why3_app_slash_boss_3d/PROOF.bend --prove --prover z3 --prover alt-ergo --timeout 1
```

These commands check proofs without running main. See the [integration guide](../../guide/WHY3.md) for setup, export commands and the trusted ATP boundary.
