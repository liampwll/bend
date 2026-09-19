# io_http_fetch: Why3 companion

The suffix law uses the previously checked constructive suffix lemma through Why3. The string-walking induction remains manual; this does not reduce the proof's line count.

[Original proof](../io_http_fetch/PROOF.bend) · [Companion proof](PROOF.bend) · [All comparisons](../why3/README.md)

Proof file: **26 → 26 code lines** (0.0% reduction); **962 → 943 code bytes**. 1 ATP obligations checked; 1 include earlier verified facts.

Every original specification, program and asset is copied byte for byte. Counts exclude blank lines and full-line comments, include imports and helper definitions, and exclude this documentation.

From the repository root, after registering Z3 and Alt-Ergo with Why3:

```sh
bun bend2/main.ts demos/why3_io_http_fetch/PROOF.bend --prove --prover z3 --prover alt-ergo --timeout 1
```

These commands check proofs without running main. See the [integration guide](../../guide/WHY3.md) for setup, export commands and the trusted ATP boundary.
