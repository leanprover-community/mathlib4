import Mathlib.Tactic.Linter.DependentTypeclass
import Mathlib.Algebra.Ring.Defs

set_option linter.dependentTypeclass false

/--
warning: Typeclass '[Mul X]' is implied by [[Ring X]]
note: this linter can be disabled with `set_option linter.dependentTypeclass false`
-/
#guard_msgs in
set_option linter.dependentTypeclass true in
variable {X : Type*} [Ring X] [Mul X]

-- this checks that binder update it allowed
set_option linter.dependentTypeclass true
variable {Y : Type*} [Add Y]
#guard_msgs in
variable (Y) [Add Y]
