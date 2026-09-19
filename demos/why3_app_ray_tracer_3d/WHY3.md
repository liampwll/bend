# app_ray_tracer_3d: Why3 companion

A general set/get lemma is automatic. Put the index first so induction generalizes the held-key list, then reuse that lemma in the original law. Esc still checks by computation.

[Original proof](../app_ray_tracer_3d/PROOF.bend) · [Companion proof](PROOF.bend) · [All comparisons](../why3/README.md)

Proof file: **15 → 10 code lines** (33.3% reduction); **314 → 276 code bytes**. 1 ATP obligations checked; 0 include earlier verified facts.

Every original specification, program and asset is copied byte for byte. Counts exclude blank lines and full-line comments, include imports and helper definitions, and exclude this documentation.

From the repository root, after registering Z3 and Alt-Ergo with Why3:

```sh
bun bend2/main.ts demos/why3_app_ray_tracer_3d/PROOF.bend --prove --prover z3 --prover alt-ergo --timeout 1 --induct k
```

These commands check proofs without running main. See the [integration guide](../../guide/WHY3.md) for setup, export commands and the trusted ATP boundary.
