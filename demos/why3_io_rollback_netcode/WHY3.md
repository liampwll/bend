# io_rollback_netcode: Why3 companion

No proof file or laws in the original, so there is no proof-size baseline. All four Bend modules are copied and checked without running the networked program.

[Original demo](../io_rollback_netcode/README.md) · [All comparisons](../why3/README.md)

No original proof file. 0 ATP obligations checked; 0 include earlier verified facts.

Every original specification, program and asset is copied byte for byte. Counts exclude blank lines and full-line comments, include imports and helper definitions, and exclude this documentation.

From the repository root, after registering Z3 and Alt-Ergo with Why3:

```sh
bun bend2/main.ts demos/why3_io_rollback_netcode/netcode.bend --prove --prover z3 --prover alt-ergo --timeout 1
bun bend2/main.ts demos/why3_io_rollback_netcode/server.bend --prove --prover z3 --prover alt-ergo --timeout 1
bun bend2/main.ts demos/why3_io_rollback_netcode/walkers_demo.bend --prove --prover z3 --prover alt-ergo --timeout 1
bun bend2/main.ts demos/why3_io_rollback_netcode/walkers_test.bend --prove --prover z3 --prover alt-ergo --timeout 1
```

These commands check proofs without running main. See the [integration guide](../../guide/WHY3.md) for setup, export commands and the trusted ATP boundary.
