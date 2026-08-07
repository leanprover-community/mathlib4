import Mathlib.Tactic.Linter.UniverseMVar
import Mathlib.Tactic.TypeStar

set_option linter.universeMVarInVariable true

universe v u

variable (C : Type*) (D : Type u)

class Foo (X : Type u) where
  P : Type v

section
/--
warning: type of variable contains universe metavariable! Foo C

Note: This linter can be disabled with `set_option linter.universeMVarInVariable false`
-/
#guard_msgs in
variable [Foo C]
end

section
variable [Foo.{v} C]
end

section
variable {D} [Foo.{v} C]
end

section
variable {D}
variable [Foo.{v} D]
end

section
variable {D} [Foo.{v} D]
end

section
/--
warning: type of variable contains universe metavariable! Foo D

Note: This linter can be disabled with `set_option linter.universeMVarInVariable false`
-/
#guard_msgs in
variable {D} [Foo D]
end
