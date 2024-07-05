import Mathlib.Tactic.MinImports
import Mathlib.Tactic

set_option linter.hashCommand true

/--
info: ℤ : Type
---
info: import Mathlib.Init.Data.Int.Basic
-/
#guard_msgs in
#min_imps #check ℤ

/-- info: import Mathlib.Init.Data.Int.Basic -/
#guard_msgs in
#min_imps ℤ

/--
info:
import Batteries.Tactic.Init
import Batteries.Tactic.PermuteGoals
import Mathlib.Tactic.ExtractGoal
-/
#guard_msgs in
#min_imps (← `(tactic| extract_goal; on_goal 1 => _))

/-- info: import Mathlib.Tactic.NormNum.Basic -/
#guard_msgs in
#min_imps
lemma uses_norm_num : (0 + 1 : ℕ) = 1 := by norm_num

/-- info: import Mathlib.Tactic.NormNum.Basic -/
#guard_msgs in
#min_imps uses_norm_num
