# why3: Valid
# why3-induct: xs
import Base

type Tree is Data:
  Leaf{value: Nat}
  Fork{left: Tree, right: Tree}

def leaves(t: Tree) -> Nat:
  match t:
    case Leaf{x}:
      1n
    case Fork{a, b}:
      Nat.add(leaves(a), leaves(b))

law fork:
  for a: Tree
  for b: Tree
  {leaves(Fork{a, b}) == Nat.add(leaves(a), leaves(b)) : Nat}

law length_append_nil:
  for xs: List<Nat>
  {List.length(&1, Nat, List.append(&1, Nat, xs, Nil{})) == List.length(&1, Nat, xs) : Nat}

law length_append:
  for xs: List<Nat>
  for ys: List<Nat>
  {List.length(&1, Nat, List.append(&1, Nat, xs, ys)) == Nat.add(List.length(&1, Nat, xs), List.length(&1, Nat, ys)) : Nat}

law pair:
  for p: Nat & Nat
  {p == p : Nat & Nat}

law other_list_instance:
  for xs: List<U32>
  {List.append(&1, U32, xs, Nil{}) == xs : List<U32>}

#|Error: 5 TODOs found.
#|The code is incomplete, and not a valid proof yet.
#|exit 1
