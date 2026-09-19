# why3: Valid
import Base

law add_zero:
  for n: Nat
  {Nat.add(n, 0n) == n : Nat}

law nat_sub_saturates:
  {Nat.sub(2n, 3n) == 0n : Nat}

law commutative:
  for a: U32
  for b: U32
  {U32.add(a, b) == U32.add(b, a) : U32}

law wrap:
  {U32.add(4294967295, 1) == 0 : U32}

law subtract_wrap:
  {U32.sub(0, 1) == 4294967295 : U32}

law div_zero:
  for x: U32
  {U32.div(x, 0) == 0 : U32}

law mod_zero:
  for x: U32
  {U32.mod(x, 0) == x : U32}

law bitwise:
  for x: U32
  {U32.xor(x, x) == 0 : U32}

law greater:
  {U32.is_gt(2, 1) == True{} : Bool}

law greater_equal:
  {U32.is_ge(2, 2) == True{} : Bool}

law shift_right:
  {U32.shr(2147483648) == 1073741824 : U32}

law shift_left:
  {U32.shl(2147483648) == 0 : U32}

#|Error: 12 TODOs found.
#|The code is incomplete, and not a valid proof yet.
#|exit 1
