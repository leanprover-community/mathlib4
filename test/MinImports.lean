import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.FunProp.Attr

open Lean.Elab.Command Mathlib.Command.MinImports in
run_cmd liftTermElabM do
  guard ([`A, `A.B.C_3, `A.B.C_2, `A.B.C_1, `A.B.C_0, `A.B.C].map previousInstName
      == [`A, `A.B.C_2, `A.B.C_1, `A.B.C,   `A.B.C,   `A.B.C])

/-- info: import Mathlib.Tactic.FunProp.Attr -/
#guard_msgs in
#min_imports in (← `(declModifiers|@[fun_prop]))

namespace X
/-- info: import Mathlib.Algebra.Ring.Nat -/
#guard_msgs in
#min_imports in
protected def xxx : Semiring Nat := inferInstance
end X

/-- info: import Mathlib.Algebra.Ring.Nat -/
#guard_msgs in
#min_imports in
-- If `#min_imports` were parsing just the syntax, the imports would be `Mathlib.Algebra.Ring.Defs`.
instance : Semiring Nat := inferInstance

/-- info: import Mathlib.Algebra.Ring.Nat -/
#guard_msgs in
#min_imports in
instance withName : Semiring Nat := inferInstance

/-- info: import Mathlib.Algebra.Ring.Nat -/
#guard_msgs in
#min_imports in
noncomputable instance : Semiring Nat := inferInstance

/--
info: ℤ : Type
---
info: import Mathlib.Data.Int.Notation
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

set_option linter.minImports.increases false
set_option linter.minImports true
/--
warning: Imports increased to
[Init.Guard, Mathlib.Data.Int.Notation]

New imports: [Init.Guard, Mathlib.Data.Int.Notation]

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
[Init.Guard, Mathlib.Data.Int.Notation]

New imports: [Init.Guard, Mathlib.Data.Int.Notation]

note: this linter can be disabled with `set_option linter.minImports false`
-/
#guard_msgs in
-- again, the imports pick-up, after the reset
set_option linter.minImports true in
#guard (0 : ℤ) = 0

-- finally, we leave the linter "on", to give it a chance to parse `eoi`
-- and to silence it, we make sure to put in a command for each import

set_option linter.minImports true

/--
warning: Imports increased to
[Mathlib.Tactic.Linter.MinImports]

New imports: [Mathlib.Tactic.Linter.MinImports]

note: this linter can be disabled with `set_option linter.minImports false`
-/
#guard_msgs in
#reset_min_imports

/--
warning: Imports increased to
[Mathlib.Tactic.FunProp.Attr, Mathlib.Tactic.NormNum.Basic]

New imports: [Mathlib.Tactic.FunProp.Attr, Mathlib.Tactic.NormNum.Basic]

Now redundant: [Mathlib.Tactic.Linter.MinImports]

note: this linter can be disabled with `set_option linter.minImports false`
-/
#guard_msgs in
run_cmd
  let _ ← `(declModifiers|@[fun_prop])
  let _ ← `(tactic|apply @Mathlib.Meta.NormNum.evalNatDvd <;> extract_goal)
