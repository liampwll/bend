import Base

# A small kernel context need not contain Nat.add, the prelude marker.
# Local hypothesis translation must still use the complete visible context.
def swap(-x: U32, -y: U32, h: {x == y : U32}) -> {y == x : U32}:
  ?auto

#|All terms check.
#|Why3 proved 1 obligation (trusted ATP evidence).
