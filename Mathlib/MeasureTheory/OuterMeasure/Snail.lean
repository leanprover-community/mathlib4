import Mathlib

structure MonsterGrid where
  IsMonster : Fin 2022 → Fin 2023 → Prop
  -- state there is exactly one per row
  -- state there is at most one per column

structure Attempt where
  positions : List ((Unit ⊕ Fin 2022 ⊕ Unit) × Fin 2023)
  -- state that consecutive positions are adjacent

structure Protocol where
  nextPos : List Attempt → Attempt → (Unit ⊕ Fin 2022 ⊕ Unit) × Fin 2023
  -- state that this is adjacent to the last position

def Protocol.run : ℕ → List Attempt → Attempt × List Attempt
  | 0, _ => sorry -- the attempt where nothing was done
  | t + 1, pastAttempts =>
    if True -- current position is not a monster
    then sorry -- the attempt at time `t` + `nextPos pastAttempts (run pastAttempts t)`
    else ((run t pastAttempts).1, (run t pastAttempts).1 :: pastAttempts)


-- prove that no position in `run` (except the last of an attempt possibly) is a monster
-- prove that `run` takes at least 2022 attempts before succeeding for all `MonsterGrid`
