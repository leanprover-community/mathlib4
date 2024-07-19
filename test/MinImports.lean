import Mathlib.Tactic.MinImports
import Mathlib.Tactic.ExtractGoal
import Mathlib.Tactic.Lemma
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Int.Notation
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.FunProp

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

/--
warning: Imports increased to
[Init.Guard, Lean.Parser.Term, Mathlib.Data.Int.Notation]
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
