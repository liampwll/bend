# Why3 proves the arithmetic lemmas and closes local contradictions.
# The division proof keeps its induction and explicit witnesses, using
# automatic arithmetic and the checked le_eq theorem in wrap_eq.
import Base
import ./main.bend as Num
import ./LAWS.bend as Laws

# Addition
# --------

def add_zero(a: Nat) -> {a == Num.add(a, 0n) : Nat}:
  ?auto

def add_succ(a: Nat, -b: Nat) -> {1n+Num.add(a, b) == Num.add(a, 1n+b) : Nat}:
  ?auto

def Laws.add_comm(a, b):
  ?auto

def Laws.add_assoc(a, b, c):
  ?auto

# Multiplication
# --------------

# the middle terms of a triple sum swap
def add_swap(x: Nat, +y: Nat, +z: Nat) -> {Num.add(x, Num.add(y, z)) == Num.add(y, Num.add(x, z)) : Nat}:
  ?auto

def mul_zero(a: Nat) -> {Num.mul(a, 0n) == 0n : Nat}:
  ?auto

def mul_succ(+a: Nat, +b: Nat) -> {Num.add(a, Num.mul(a, b)) == Num.mul(a, 1n+b) : Nat}:
  ?auto

def Laws.mul_comm(a, b):
  ?auto

def Laws.mul_dist(a, b, c):
  ?auto

# Division
# --------

# a remainder at most m that is not below m is m
def le_eq(r: Nat, m: Nat, le: {True{} == (r < 1n+m) : Bool}, e: {False{} == (r < m) : Bool}) -> {r == m : Nat}:
  match r m:
    case 0n 0n:
      {==}
    case 0n 1n+b:
      ?auto
    case 1n 0n:
      ?auto
    case 2n+a 0n:
      ?auto
    case 1n+a 1n+b:
      %le_eq(a, b, le, e) : {1n+a == 1n+_ : Nat}
      {==}

# Ok(n, m, qr): qr is Euclid's quotient and remainder of n by 1n+m
def Ok(n: Nat, m: Nat, qr: Nat & Nat) -> Type:
  &q: Nat -> &r: Nat -> {(q, r) == qr : Nat & Nat} & {True{} == (r < 1n+m) : Bool} & {n == Num.add(r, Num.mul(q, 1n+m)) : Nat}

# the wrap arm: r has reached m, so 1n+q and 0n rebuild 1n+p
def wrap_eq(-p: Nat, m: Nat, -q: Nat, r: Nat, le: {True{} == (r < 1n+m) : Bool}, e: {False{} == (r < m) : Bool}, eq: {p == Num.add(r, Num.mul(q, 1n+m)) : Nat})
  -> {1n+p == Num.add(0n, Num.mul(1n+q, 1n+m)) : Nat}:
  ?auto

# the step keeps Ok, decided on the verdict b of r < m
def wrap_ok(-p: Nat, m: Nat, q: Nat, +r: Nat, le: {True{} == (r < 1n+m) : Bool}, eq: {p == Num.add(r, Num.mul(q, 1n+m)) : Nat}, b: Bool, e: {b == (r < m) : Bool})
  -> Ok(1n+p, m, Num.divmod.wrap(b, q, r)):
  match b:
    case True{}:
      (q, 1n+r, {==}, e, Equal.cong(Nat, Nat, k => 1n+k, p, Num.add(r, Num.mul(q, 1n+m)), eq))
    case False{}:
      (1n+q, 0n, {==}, {==}, wrap_eq(p, m, q, r, le, e, eq))

# opens the certificate of divmod.go(p, m) and runs it through wrap_ok
def step_ok(-p: Nat, +m: Nat, w: Ok(p, m, Num.divmod.go(p, m))) -> Ok(1n+p, m, Num.divmod.step(m, Num.divmod.go(p, m))):
  (q, r0, dq, le, eq) = w
  +r = r0
  %dq : Ok(1n+p, m, Num.divmod.step(m, _))
  wrap_ok(p, m, q, r, le, eq, (r < m), {==})

def Laws.divmod_ok(n, m):
  match n:
    case 0n:
      (0n, 0n, {==}, {==}, {==})
    case 1n+p:
      step_ok(p, m, Laws.divmod_ok(p, m))
