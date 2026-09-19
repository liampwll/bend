# Safety keeps coordinates inside the map, outside the sealed room,
# off walls and not won. Bounds are explicit because coordinates use Nat.
# Why3 proves the four lemmas; the final proofs just reuse them.
import Base
import ./main.bend as Game
import ./LAWS.bend as Laws

def safe(g: Game.Game) -> Bool:
  Game.Game{+x, +y, won} = g
  Bool.not(won) && ((Game.nat_le(x, 11n) && Game.nat_le(y, 7n))
    && (Bool.not(Game.nat_le(x, 2n) && Game.nat_le(y, 2n)) && Bool.not(Game.wall(x, y))))

law safe_not_won:
  for -g: Game.Game
  for h: {safe(g) == True{} : Bool}
  {Game.is_won(g) == False{} : Bool}

# This checks Laws.at_flag: indexing the actual string returned by grid.
# It is not a replacement assertion about the logical on_flag predicate.
law safe_not_flag:
  for -g: Game.Game
  for h: {safe(g) == True{} : Bool}
  {Laws.at_flag(g) == False{} : Bool}

law step_safe:
  for -m: Game.Move
  for -g: Game.Game
  for h: {safe(g) == True{} : Bool}
  {safe(Game.step(m, g)) == True{} : Bool}

# Induction on the move list plays the role of the loop invariant.
law run_safe:
  for moves: List<Game.Move>
  for g: Game.Game
  for h: {safe(g) == True{} : Bool}
  {safe(Game.run(moves, g)) == True{} : Bool}

def Laws.you_cant_win(moves):
  safe_not_won(Game.replay(Game.start(), moves), run_safe(moves, Game.start(), {==}))

def Laws.never_on_flag(moves):
  safe_not_flag(Game.replay(Game.start(), moves), run_safe(moves, Game.start(), {==}))
