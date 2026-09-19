# Run normally: bend demos/proof_why3/PROOF.bend
# The imported open laws are proved automatically, then used below.
import ./LAWS.bend as Laws
import Base

# The easy lemma is now a usable theorem, with no handwritten induction.
def use_add_zero(n: Nat) -> {Nat.add(n, 0n) == n : Nat}:
  Laws.add_zero(n)

# A local automatic step can use previously verified lemmas too.
def nested_zero(n: Nat) -> {Nat.add(Nat.add(n, 0n), 0n) == n : Nat}:
  ?auto

# A full proof can combine manual structure with an automatic subgoal.
def congruent(a: Nat, b: Nat, h: {a == b : Nat}) -> {Nat.add(a, 0n) == b : Nat}:
  %p@h : {Nat.add(a, 0n) == _ : Nat}
  ?auto

# Opaque existential facts can be eliminated inside proofs. The ATP does not
# compute the witness: executable code must supply its own Bend witness.
law use_existence:
  for n: Nat
  exs m: Nat
  {m == 1n+n : Nat}

def use_existence(n):
  Laws.successor_witness(n)

# Rewrites using automated evidence erase just like ordinary equality proofs.
def main() -> Nat:
  %p@Laws.add_zero(3n) : Nat
  42n
