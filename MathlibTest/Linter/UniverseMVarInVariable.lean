import Mathlib.Tactic.Linter.UniverseMVar
import Mathlib.Tactic.TypeStar
import Mathlib.Algebra.Group.Action.Defs

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
/--
warning: type of variable contains universe metavariable! Foo C

Note: This linter can be disabled with `set_option linter.universeMVarInVariable false`
-/
#guard_msgs in
variable {h0 : Foo C}

/--
warning: type of variable contains universe metavariable! Foo C

Note: This linter can be disabled with `set_option linter.universeMVarInVariable false`
-/
#guard_msgs in
variable ⦃h1 : Foo C⦄

/--
warning: type of variable contains universe metavariable! Foo C

Note: This linter can be disabled with `set_option linter.universeMVarInVariable false`
-/
#guard_msgs in
variable [h2 : Foo C]

/--
warning: type of variable contains universe metavariable! Foo C

Note: This linter can be disabled with `set_option linter.universeMVarInVariable false`
-/
#guard_msgs in
variable (h3 : Foo C)
end

section
variable {h0 : Foo.{v} C}
variable ⦃h1 : Foo.{v} C⦄
variable [h2 : Foo.{v} C]
variable (h3 : Foo.{v} C)
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

variable {D} (D) {D} (D)

variable {α β : Type*}
section
variable [DecidableEq β] [Group α] [MulAction α β]
example (a : α) (b : β) : a • b = a • b := rfl
end
