# why3: Reject @unsafe dependency
import Base

@unsafe
def bad(n: Nat) -> Nat:
  bad(n)

law exploit:
  for n: Nat
  {bad(n) == 0n : Nat}

#|Error: 1 TODO found.
#|The code is incomplete, and not a valid proof yet.
#|exit 1
