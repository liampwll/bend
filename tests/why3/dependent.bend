# why3: Reject dependent
import Base

law indexed:
  for n: Nat
  for w: Word(n)
  {w == w : Word(n)}

#|Error: 1 TODO found.
#|The code is incomplete, and not a valid proof yet.
#|exit 1
