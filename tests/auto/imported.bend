import ./lemmas.bend as Facts
import Base

def imported(n: Nat) -> {Nat.add(n, 0n) == n : Nat}:
  Facts.right_zero(n)

def inferred(n: Nat) -> {Nat.add(Nat.add(n, 0n), 0n) == n : Nat}:
  ?auto

#|All terms check.
#|Why3 proved 5 obligations (trusted ATP evidence).
