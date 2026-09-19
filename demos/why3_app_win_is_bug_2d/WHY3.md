# app_win_is_bug_2d: Why3 companion

One bounded safety invariant replaces the finite-map certificate and its Boolean proof kit. Why3 proves that safety implies both observations, that a step preserves safety, and that any move list preserves it. The final proofs apply these theorems. The rendered-flag claim still indexes the actual grid string; neither law nor the game is changed.

[Original proof](../app_win_is_bug_2d/PROOF.bend) · [Companion proof](PROOF.bend) · [All comparisons](../why3/README.md)

Proof file: **391 → 29 code lines** (92.6% reduction); **15288 → 1017 code bytes**. 4 ATP obligations checked; 1 include earlier verified facts.

Every original specification, program and asset is copied byte for byte. Counts exclude blank lines and full-line comments, include imports and helper definitions, and exclude this documentation.

From the repository root, after registering Z3 and Alt-Ergo with Why3:

```sh
bun bend2/main.ts demos/why3_app_win_is_bug_2d/PROOF.bend --prove --prover z3 --prover alt-ergo --timeout 1
```

These commands check proofs without running main. See the [integration guide](../../guide/WHY3.md) for setup, export commands and the trusted ATP boundary.
