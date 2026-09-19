# Check: bend demos/proof_why3/LAWS.bend
# Use the results: bend demos/proof_why3/PROOF.bend
# Export: bend demos/proof_why3/LAWS.bend -o laws.mlw
import Base

# Why3 finds a structural induction on n.
law add_zero:
  for n: Nat
  {Nat.add(n, 0n) == n : Nat}

# Word arithmetic wraps, as it does in Bend's runtime.
law wrap:
  {U32.add(4294967295, 1) == 0 : U32}

# Proof parameters express preconditions.
law increment_zero:
  for n: Nat
  for precondition: {n == 0n : Nat}
  {Nat.add(n, 1n) == 1n : Nat}

# Existential goals do not need a manually supplied witness in this workflow.
law successor_witness:
  for n: Nat
  exs m: Nat
  {m == 1n+n : Nat}
