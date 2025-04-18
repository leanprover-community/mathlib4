import Mathlib.Tactic.Linter.DependentTypeclass
import Mathlib.Algebra.Ring.Defs
set_option autoImplicit false

namespace X
/--
warning: Typeclass '[Mul E]' follows from '{E} [Group E]'
note: this linter can be disabled with `set_option linter.dependentTypeclass false`
---
warning: Typeclass '[Inv E]' follows from '{E} [Group E]'
note: this linter can be disabled with `set_option linter.dependentTypeclass false`
-/
#guard_msgs in
set_option pp.rawOnError true in
variable {E} [Add E] [Mul E] [Group E] [Inv E]

set_option linter.dependentTypeclass false
variable {X Y Z : Type*}

/--
warning: Typeclass '[Mul X]' follows from '{X} [Ring X]'
note: this linter can be disabled with `set_option linter.dependentTypeclass false`
-/
#guard_msgs in
set_option linter.dependentTypeclass true in
variable [Ring X] [Mul X]

-- this checks that binder update it allowed
set_option linter.dependentTypeclass true
variable [Add Y]
#guard_msgs in
variable (Y) [Add Y]

variable [Semigroup Z]
/--
warning: Typeclass '[Semigroup Z]' follows from '{Z} [MonoidWithZero Z]'
note: this linter can be disabled with `set_option linter.dependentTypeclass false`
---
info: The assumptions '{Z} [MonoidWithZero Z]' imply the earlier assumption '[Semigroup Z]'
-/
#guard_msgs in
variable [MonoidWithZero Z]
variable [Group Z]
