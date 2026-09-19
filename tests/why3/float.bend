# why3: Reject F32 is outside
import Base

law floats:
  for f: F32
  {f == f : F32}

#|Error: 1 TODO found.
#|The code is incomplete, and not a valid proof yet.
#|exit 1
