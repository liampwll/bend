import Base

type Single is Data:
  Only{}

def transport(a: Nat, b: Nat, h: {a == b : Nat}) -> {b == a : Nat}:
  ?auto

def impossible(n: Nat, h: {0n == 1n+n : Nat}) -> {0n == 1n+n : Nat}:
  ?auto

# An easy automatic step must leave h available for the second component.
def reuse(n: Nat, h: {n == n : Nat}) -> {n == n : Nat} & {n == n : Nat}:
  (?auto, h)

# A singleton's value is fixed; its equality needs no hypothesis either.
def singleton(u: Single, h: {0n == 0n : Nat}) -> {u == Only{} : Single} & {0n == 0n : Nat}:
  (?auto, h)

#|All terms check.
#|Why3 proved 4 obligations (trusted ATP evidence).
