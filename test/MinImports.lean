import Mathlib.Tactic.MinImports
import Mathlib.Tactic.ExtractGoal
import Mathlib.Tactic.Lemma
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Int.Notation
import Mathlib.Tactic.NormNum.Basic

/--
info: ℤ : Type
---
info: import Lean.Parser.Command
import Mathlib.Data.Int.Notation
-/
#guard_msgs in
#min_imports in #check ℤ

/-- info: import Mathlib.Data.Int.Notation -/
#guard_msgs in
#min_imports in ℤ

/--
info:
import Batteries.Tactic.Init
import Batteries.Tactic.PermuteGoals
import Mathlib.Tactic.ExtractGoal
-/
#guard_msgs in
#min_imports in (← `(tactic| extract_goal; on_goal 1 => _))

/-- info: import Mathlib.Tactic.NormNum.Basic -/
#guard_msgs in
#min_imports in
lemma uses_norm_num : (0 + 1 : ℕ) = 1 := by norm_num

/-- info: import Mathlib.Tactic.NormNum.Basic -/
#guard_msgs in
#min_imports in uses_norm_num

/--
info: theorem extracted_1 (n : ℕ) : n = n := sorry
---
info: import Mathlib.Tactic.ExtractGoal
import Mathlib.Tactic.Lemma
import Mathlib.Data.Nat.Notation
-/
#guard_msgs in
#min_imports in
lemma hi (n : ℕ) : n = n := by extract_goal; rfl
