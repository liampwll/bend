# why3: Reject TODO holes
import Base

law unfinished:
  for n: Nat
  {n == n : Nat}

def unfinished(n):
  ?TODO

#|Error: 1 TODO found.
#|The code is incomplete, and not a valid proof yet.
#|exit 1
