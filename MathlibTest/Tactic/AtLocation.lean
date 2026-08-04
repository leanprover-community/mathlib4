import Mathlib.Tactic.NormNum
import Mathlib.Tactic.ReduceModChar

-- A contradiction found in the first listed hypothesis must stop `norm_num`
-- before it tries to process later locations on the already-closed goal.
example (h : 0 = 1) (_h2 : 0 = 2) : False := by
  norm_num at h _h2

-- `reduce_mod_char` uses the same location helper. It normalizes hypotheses
-- instead of closing the goal, so the empty-goal break does not fire; several
-- listed locations (and the target) must still all be processed.
example (a : ZMod 7) (h : a + 14 = 2) (h2 : a + 21 = 2) : a + 7 = 2 := by
  reduce_mod_char at h h2 ⊢
  assumption
