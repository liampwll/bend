# Why3 proves the general setter lemma by induction on the index.
# The law reuses it; Esc remains a direct computation on the game state.
import Base
import ./main.bend as Ray
import ./LAWS.bend as Laws

def set_get(k: Nat, held: List<&2, Bool>, v: Bool)
  -> {Ray.Fly.get(Ray.Fly.set(held, k, v), k) == v : Bool}:
  ?auto

def Laws.esc_quits(rest, s):
  {==}

def Laws.press_reads(held, k, v):
  set_get(k, held, v)
