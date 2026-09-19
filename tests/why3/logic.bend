# why3: Valid
import Base

law assumption:
  for x: Nat
  for h: {x == 0n : Nat}
  {Nat.add(x, 1n) == 1n : Nat}

law transitive:
  for x: Nat
  for y: Nat
  for z: Nat
  {x == y : Nat} -> {y == z : Nat} -> {x == z : Nat}

law disjunction:
  for b: Bool
  {b == True{} : Bool} | {b == False{} : Bool}

law witnesses:
  for n: Nat
  exs m: Nat
  {n == m : Nat}

law conjunction:
  {0n == 0n : Nat} & {1n == 1n : Nat}

law literal_neq:
  {0n != 1n : Nat}

law truth:
  Unit

#|Error: 7 TODOs found.
#|The code is incomplete, and not a valid proof yet.
#|exit 1
