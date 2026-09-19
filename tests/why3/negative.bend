# why3: Reject higher-order
import Base

type Negative is Type:
  Neg{run: Negative -> Empty}

law negative:
  for x: Negative
  {x == x : Negative}

#|Error: 1 TODO found.
#|The code is incomplete, and not a valid proof yet.
#|exit 1
