# Why3 proves the imported last_press law automatically.
# Esc still checks by computation over the full game state.
import Base
import ./main.bend as Game
import ./LAWS.bend as Laws

def Laws.esc_quits(rest, g):
  {==}
