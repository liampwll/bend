# Why3 proves the arithmetic and Boolean helper lemmas.
# The dependent tree proofs keep their inductions and reuse those facts.
import Base
import ./main.bend as Sort
import ./LAWS.bend as Laws

def add_zero(a: Nat) -> {a == Nat.add(a, 0n) : Nat}:
  ?auto

def add_succ(a: Nat, -b: Nat) -> {1n+Nat.add(a, b) == Nat.add(a, 1n+b) : Nat}:
  ?auto

def add_comm(a: Nat, +b: Nat) -> {Nat.add(a, b) == Nat.add(b, a) : Nat}:
  ?auto

def add_swap(x: Nat, +y: Nat, +z: Nat) -> {Nat.add(x, Nat.add(y, z)) == Nat.add(y, Nat.add(x, z)) : Nat}:
  ?auto

def add_regroup(a: Nat, b: Nat, c: Nat, d: Nat)
  -> {Nat.add(Nat.add(a, b), Nat.add(c, d)) == Nat.add(Nat.add(a, c), Nat.add(b, d)) : Nat}:
  ?auto

def mix_leaf(s: Bool, c: Bool, +x: Nat, +y: Nat)
  -> {Nat.add(x, y) == Nat.add(Sort.pick(Nat, Bool.xor(s, c), x, y), Sort.pick(Nat, Bool.xor(Bool.not(s), c), x, y)) : Nat}:
  ?auto

def Laws.mix_leaves(d, s, x, y):
  match d:
    case 0n:
      mix_leaf(s, Nat.is_lt(y, x), x, y)
    case 1n++p:
      (+xl, +xr) = x
      (+yl, +yr) = y
      +a = Sort.sum(p, Sort.mix(p, s, xl, yl))
      +b = Sort.sum(p, Sort.mix(p, s, xr, yr))
      +c = Sort.sum(p, Sort.mix(p, Bool.not(s), xl, yl))
      +d = Sort.sum(p, Sort.mix(p, Bool.not(s), xr, yr))
      +e = Sort.sum(p, xl)
      +f = Sort.sum(p, xr)
      +g = Sort.sum(p, yl)
      +h = Sort.sum(p, yr)
      %add_regroup(e, g, f, h) : {_ == Nat.add(Nat.add(a, b), Nat.add(c, d)) : Nat}
      %add_regroup(a, c, b, d) : {Nat.add(Nat.add(e, g), Nat.add(f, h)) == _ : Nat}
      %Laws.mix_leaves(p, s, xl, yl) : {Nat.add(Nat.add(e, g), Nat.add(f, h)) == Nat.add(_, Nat.add(b, d)) : Nat}
      %Laws.mix_leaves(p, s, xr, yr) : {Nat.add(Nat.add(e, g), Nat.add(f, h)) == Nat.add(Nat.add(e, g), _) : Nat}
      {==}

def sum_flow(+d: Nat, +s: Bool, +t: Sort.Tree(d)) -> {Sort.sum(d, t) == Sort.sum(d, Sort.flow(d, s, t)) : Nat}:
  match d:
    case 0n:
      {==}
    case 1n++p:
      (+x, +y) = t
      %sum_flow(p, s, Sort.mix(p, s, x, y)) : {Nat.add(Sort.sum(p, x), Sort.sum(p, y)) == Nat.add(_, Sort.sum(p, Sort.flow(p, s, Sort.mix(p, Bool.not(s), x, y)))) : Nat}
      %sum_flow(p, s, Sort.mix(p, Bool.not(s), x, y)) : {Nat.add(Sort.sum(p, x), Sort.sum(p, y)) == Nat.add(Sort.sum(p, Sort.mix(p, s, x, y)), _) : Nat}
      Laws.mix_leaves(p, s, x, y)

def Laws.sort_leaves(d, s, t):
  match d:
    case 0n:
      {==}
    case 1n++p:
      (+x, +y) = t
      %sum_flow(1n+p, s, (Sort.sort(p, True{}, x), Sort.sort(p, False{}, y))) : {Nat.add(Sort.sum(p, x), Sort.sum(p, y)) == _ : Nat}
      %Laws.sort_leaves(p, True{}, x) : {Nat.add(Sort.sum(p, x), Sort.sum(p, y)) == Nat.add(_, Sort.sum(p, Sort.sort(p, False{}, y))) : Nat}
      %Laws.sort_leaves(p, False{}, y) : {Nat.add(Sort.sum(p, x), Sort.sum(p, y)) == Nat.add(Sort.sum(p, x), _) : Nat}
      {==}
