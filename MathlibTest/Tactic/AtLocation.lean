import Mathlib.Tactic.NormNum
import Mathlib.Tactic.ReduceModChar

-- A contradiction found in the first listed hypothesis must stop `norm_num`
-- before it tries to process later locations on the already-closed goal.
example (h : 0 = 1) (_h2 : 0 = 2) : False := by
  norm_num at h _h2

-- `reduce_mod_char` uses the same location helper and must also stop once an
-- earlier hypothesis closes the goal.
example (h : (0 : ZMod 5) = 1) (_h2 : (0 : ZMod 5) = 2) : False := by
  reduce_mod_char at h _h2
