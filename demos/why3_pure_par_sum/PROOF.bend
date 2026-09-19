# Four automatic proofs: arithmetic facts support seq_add, which
# supports tree_is_seq. Use --induct a --induct n (see WHY3.md).
import Base
import ./main.bend as Par
import ./LAWS.bend as Laws

def add_zero(a: Nat) -> {Nat.add(a, 0n) == a : Nat}:
  ?auto

def add_assoc(a: Nat, -b: Nat, -c: Nat) -> {Nat.add(a, Nat.add(b, c)) == Nat.add(Nat.add(a, b), c) : Nat}:
  ?auto

def seq_add(n: Nat, +m: Nat, +i: Nat)
  -> {Nat.add(Par.seq(m, i), Par.seq(n, Nat.add(m, i))) == Par.seq(Nat.add(n, m), i) : Nat}:
  ?auto

def Laws.tree_is_seq(d, i):
  ?auto
