# why3: Unproved
import Base

law false_law:
  for x: U32
  {U32.add(x, 1) == x : U32}

# This must stay unproved even when another law in the same file is false.
law independent_false:
  {True{} == False{} : Bool}

#|Error: 2 TODOs found.
#|The code is incomplete, and not a valid proof yet.
#|exit 1
