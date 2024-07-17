import Mathlib.Tactic.MinImports
import Mathlib.Tactic

/--
info: ℤ : Type
---
info:
import Lean.Parser.Command
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
info: ℤ : Type
---
info: Try this: change True
---
info:
import Lean.Parser.Command
import Mathlib.Tactic.Change
import Mathlib.Tactic.Lemma
import Mathlib.Data.Int.Notation
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
import Mathlib.Data.Nat.Notation
-/
#guard_msgs in
#min_imports in
lemma hi (n : ℕ) : n = n := by extract_goal; rfl

/--
info: ℕ : Type
---
warning: Imports increased to
[Lean.Parser.Command, Mathlib.Data.Nat.Notation]
note: this linter can be disabled with `set_option linter.minImports false`
-/
#guard_msgs in
set_option linter.minImports true in
#check ℕ

/--
warning: Imports increased to
[Init.Guard, Lean.Parser.Command, Mathlib.Data.Int.Notation, Mathlib.Data.Nat.Notation]
note: this linter can be disabled with `set_option linter.minImports false`
-/
#guard_msgs in
set_option linter.minImports true in
#guard (0 : ℤ) = 0

#guard_msgs in
-- no new imports needed here, so no message
set_option linter.minImports true in
#guard (0 : ℤ) = 0

set_option linter.minImports false in

#reset_min_imports

/--
warning: Imports increased to
[Init.Guard, Lean.Parser.Term, Mathlib.Data.Int.Notation]
note: this linter can be disabled with `set_option linter.minImports false`
-/
#guard_msgs in
-- again, the imports pick-up, after the reset
set_option linter.minImports true in
#guard (0 : ℤ) = 0
