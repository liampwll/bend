import Base

def transport(a: Nat, b: Nat, h: {a == b : Nat}) -> {b == a : Nat}:
  ?auto

def erased(-a: Nat, -b: Nat, h: {a == b : Nat}) -> {b == a : Nat}:
  ?auto

def rewrite(a: Nat, b: Nat, h: {a == b : Nat}) -> {Nat.add(a, 0n) == b : Nat}:
  %p@h : {Nat.add(a, 0n) == _ : Nat}
  ?auto

def use_affine(n: Nat) -> Nat:
  eq = {?auto : {Nat.add(n, 0n) == n : Nat}}
  %p@eq : Nat
  n

law witness:
  for n: Nat
  exs m: Nat
  {n == m : Nat}

def witness(n):
  (n, ?auto)

def cases(n: Nat) -> {Nat.add(n, 0n) == n : Nat}:
  match n:
    case Zero{}:
      ?auto
    case Succ{p}:
      ih = cases(p)
      ?auto

#|All terms check.
#|Why3 proved 7 obligations (trusted ATP evidence).
