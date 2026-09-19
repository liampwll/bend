# why3: Reject unfilled computational dependency
# why3-law: use_missing
import Base

law missing:
  for n: Nat
  Nat

law use_missing:
  for n: Nat
  {missing(n) == missing(n) : Nat}

#|Error: 2 TODOs found.
#|The code is incomplete, and not a valid proof yet.
#|exit 1
