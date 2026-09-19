# pure_hvm5_mini: Why3 companion

Automatic lexer and printer lemmas feed the remaining manual proofs. The interpreter's existing unsafe definitions are unchanged; Why3 does not admit them as premises.

[Original proof](../pure_hvm5_mini/PROOF.bend) · [Companion proof](PROOF.bend) · [All comparisons](../why3/README.md)

Proof file: **157 → 117 code lines** (25.5% reduction); **4355 → 3394 code bytes**. 7 ATP obligations checked; 2 include earlier verified facts.

Every original specification, program and asset is copied byte for byte. Counts exclude blank lines and full-line comments, include imports and helper definitions, and exclude this documentation.

From the repository root, after registering Z3 and Alt-Ergo with Why3:

```sh
bun bend2/main.ts demos/why3_pure_hvm5_mini/PROOF.bend --prove --prover z3 --prover alt-ergo --timeout 1
```

These commands check proofs without running main. See the [integration guide](../../guide/WHY3.md) for setup, export commands and the trusted ATP boundary.
