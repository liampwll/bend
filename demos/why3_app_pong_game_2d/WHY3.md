# app_pong_game_2d: Why3 companion

The imported last-press law is automatic; the four-slot helper and its 16 Boolean cases disappear. Esc still checks by computation.

[Original proof](../app_pong_game_2d/PROOF.bend) · [Companion proof](PROOF.bend) · [All comparisons](../why3/README.md)

Proof file: **52 → 5 code lines** (90.4% reduction); **1662 → 102 code bytes**. 1 ATP obligations checked; 0 include earlier verified facts.

Every original specification, program and asset is copied byte for byte. Counts exclude blank lines and full-line comments, include imports and helper definitions, and exclude this documentation.

From the repository root, after registering Z3 and Alt-Ergo with Why3:

```sh
bun bend2/main.ts demos/why3_app_pong_game_2d/PROOF.bend --prove --prover z3 --prover alt-ergo --timeout 1
```

These commands check proofs without running main. See the [integration guide](../../guide/WHY3.md) for setup, export commands and the trusted ATP boundary.
