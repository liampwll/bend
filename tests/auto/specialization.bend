import Base

def add(a: Nat, b: Nat) -> Nat:
  match a:
    case 0n: b
    case 1n+p: 1n+add(p, b)

# A fact about a fixed operand must remain available when proving the
# generic commutativity theorem, including its zero case.
law right_zero:
  for n: Nat
  {add(n, 0n) == n : Nat}

law right_succ:
  for n: Nat
  for m: Nat
  {add(n, 1n+m) == 1n+add(n, m) : Nat}

law commutative:
  for n: Nat
  for m: Nat
  {add(n, m) == add(m, n) : Nat}

#|All terms check.
#|Why3 proved 3 obligations (trusted ATP evidence).
