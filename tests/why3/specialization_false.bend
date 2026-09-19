# why3: Unproved
import Base

def le(a: Nat, b: Nat) -> Bool:
  match a b:
    case 0n _: True{}
    case 1n+p 0n: False{}
    case 1n+p 1n+q: le(p, q)

# Specializing the bound must not restrict the quantified coordinate to it.
law not_every_nat_is_bounded:
  for n: Nat
  {le(n, 3n) == True{} : Bool}

law incorrect_closed_bound:
  {le(4n, 3n) == True{} : Bool}

#|Error: 2 TODOs found.
#|The code is incomplete, and not a valid proof yet.
#|exit 1
