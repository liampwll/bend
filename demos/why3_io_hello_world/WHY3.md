# io_hello_world: Why3 companion

Unchanged: the original is one reflexivity proof of an IO expression. IO is outside the exporter.

[Original proof](../io_hello_world/PROOF.bend) · [Companion proof](PROOF.bend) · [All comparisons](../why3/README.md)

Proof file: **5 → 5 code lines** (0.0% reduction); **99 → 99 code bytes**. 0 ATP obligations checked; 0 include earlier verified facts.

Every original specification, program and asset is copied byte for byte. Counts exclude blank lines and full-line comments, include imports and helper definitions, and exclude this documentation.

From the repository root, after registering Z3 and Alt-Ergo with Why3:

```sh
bun bend2/main.ts demos/why3_io_hello_world/PROOF.bend --prove --prover z3 --prover alt-ergo --timeout 1
```

These commands check proofs without running main. See the [integration guide](../../guide/WHY3.md) for setup, export commands and the trusted ATP boundary.
