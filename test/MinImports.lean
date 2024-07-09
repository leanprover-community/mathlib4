import Mathlib.Tactic.MinImports
import Mathlib.Tactic

set_option linter.hashCommand true

/--
info: ℤ : Type
---
info: import Mathlib.Init.Data.Int.Basic
-/
#guard_msgs in
#min_imports in #check ℤ

/-- info: import Mathlib.Init.Data.Int.Basic -/
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
info: ℤ : Type
---
info: Try this: change True
---
info: import Mathlib.Tactic.Change
import Mathlib.Tactic.Lemma
import Mathlib.Init.Data.Int.Basic
-/
#guard_msgs in
#min_imports start
#check ℤ
lemma ohMy : True := by change? _; trivial
until

/--
info: theorem extracted_1 (n : ℕ) : n = n := sorry
---
info: import Mathlib.Tactic.ExtractGoal
import Mathlib.Tactic.Lemma
import Mathlib.Init.Data.Nat.Notation
-/
#guard_msgs in
#min_imports in
lemma hi (n : ℕ) : n = n := by extract_goal; rfl

/--
info: ℕ : Type
---
warning: Imports increased to
[Lean.Parser.Command, Mathlib.Init.Data.Nat.Notation]
note: this linter can be disabled with `set_option linter.minImports false`
-/
#guard_msgs in
set_option linter.minImports true in
#check ℕ

/--
warning: Imports increased to
[Init.Guard, Mathlib.Init.Data.Int.Basic]
note: this linter can be disabled with `set_option linter.minImports false`
-/
#guard_msgs in
set_option linter.minImports true in
#guard (0 : ℤ) = 0

#guard_msgs in
-- no new imports needed here, so no message
set_option linter.minImports true in
#guard (0 : ℤ) = 0

#reset_min_imports

set_option linter.minImports true

/--
warning: Imports increased to
[Init.Guard, Lean.Parser.Term, Mathlib.Init.Data.Nat.Notation]
note: this linter can be disabled with `set_option linter.minImports false`
-/
#guard_msgs in
#guard (0 : ℕ) == 0

/--
warning: Imports increased to
[Init.Guard, Mathlib.Init.Data.Int.Basic]
note: this linter can be disabled with `set_option linter.minImports false`
-/
#guard_msgs in
set_option linter.minImports true in
#guard (0 : ℤ) = 0

#guard_msgs in
-- no new imports needed here, so no message
set_option linter.minImports true in
#guard (0 : ℤ) = 0
