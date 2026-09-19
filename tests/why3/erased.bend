# why3: Reject erased quantified
import Base

law erased_evidence:
  for -p: {0n == 1n : Nat}
  {0n == 1n : Nat}

#|Error: 1 TODO found.
#|The code is incomplete, and not a valid proof yet.
#|exit 1
