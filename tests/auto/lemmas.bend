import Base

law right_zero:
  for n: Nat
  {Nat.add(n, 0n) == n : Nat}

def manual_use(n: Nat) -> {Nat.add(n, 0n) == n : Nat}:
  right_zero(n)

law twice_zero:
  for n: Nat
  {Nat.add(Nat.add(n, 0n), 0n) == n : Nat}

def local_use(n: Nat) -> {Nat.add(Nat.add(n, 0n), 0n) == n : Nat}:
  ?auto

law exists_same:
  for n: Nat
  exs m: Nat
  {n == m : Nat}

law witness_use:
  for n: Nat
  exs m: Nat
  {n == m : Nat}

def witness_use(n):
  exists_same(n)

#|All terms check.
#|Why3 proved 4 obligations (trusted ATP evidence).
