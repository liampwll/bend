# why3: Unproved
# Same names as Base, deliberately different meanings.
type U32 is Data:
  A{}
  B{}

def U32.add(x: U32, y: U32) -> U32:
  x

law not_commutative:
  {U32.add(A{}, B{}) == U32.add(B{}, A{}) : U32}

#|Error: 1 TODO found.
#|The code is incomplete, and not a valid proof yet.
#|exit 1
