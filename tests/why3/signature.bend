# why3: Valid
import Base

law identity:
  for n: Nat
  Nat

def identity(n):
  n

law identity_law:
  for n: Nat
  {identity(n) == n : Nat}

#|Error: 1 TODO found.
#|The code is incomplete, and not a valid proof yet.
#|exit 1
