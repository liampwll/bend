# why3: Valid
import Base

def le(a: Nat, b: Nat) -> Bool:
  match a b:
    case 0n _:
      True{}
    case 1n+p 0n:
      False{}
    case 1n+p 1n+q:
      le(p, q)

def small(n: Nat) -> Bool:
  match n:
    case 0n: True{}
    case 1n: True{}
    case 2n: True{}
    case 3n: True{}
    case 4n+p: False{}

# The fixed second operand unfolds to a finite decision tree.
law bounded:
  for n: Nat
  {le(n, 3n) == small(n) : Bool}

# Keep an unchanged recursive operand generic so its theorem is reusable.
law right_zero:
  for n: Nat
  {Nat.add(n, 0n) == n : Nat}

# A growing static operand must fall back to a generic recursive function.
def grow(n: Nat, acc: Nat) -> Nat:
  match n:
    case 0n: acc
    case 1n+p: grow(p, 1n+acc)

law growing:
  for n: Nat
  {grow(n, 0n) == grow(n, 0n) : Nat}

# Changing static flags must not generate an unbounded specialization cycle.
def flip(n: Nat, b: Bool) -> Bool:
  match n:
    case 0n: b
    case 1n+p: flip(p, Bool.not(b))

law toggling:
  for n: Nat
  {flip(n, True{}) == flip(n, True{}) : Bool}

# Preserve the type annotation when a specialized constructor belongs to a
# parameterized datatype; a bare None constructor cannot determine its type.
def absent(m: Maybe<Nat>) -> Bool:
  match m:
    case None{}: True{}
    case Some{n}: False{}

law closed_maybe:
  {absent(None{}) == True{} : Bool}

#|Error: 5 TODOs found.
#|The code is incomplete, and not a valid proof yet.
#|exit 1
