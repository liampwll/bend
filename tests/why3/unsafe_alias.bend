# why3: Reject @unsafe dependency
import Base

@unsafe
def Alias() -> Data:
  Nat

law alias_law:
  for x: Alias()
  {x == x : Alias()}

#|Error: 1 TODO found.
#|The code is incomplete, and not a valid proof yet.
#|exit 1
