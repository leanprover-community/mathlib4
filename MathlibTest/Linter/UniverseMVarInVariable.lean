import Mathlib.Tactic.Linter.UniverseMVar
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Tactic.CategoryTheory.CategoryStar

set_option linter.universeMVarInVariable true

universe v u

open CategoryTheory

#guard_msgs in
variable (n m : Nat) (m : Nat) (C : Type*) (D : Type*)

/--
warning: type of variable contains universe metavariable! Category.{_, u_1} C

Note: This linter can be disabled with `set_option linter.universeMVarInVariable false`
---
warning: type of variable contains universe metavariable! Category.{_, u_2} D

Note: This linter can be disabled with `set_option linter.universeMVarInVariable false`
-/
#guard_msgs in
variable [Category C] [Category D]

#guard_msgs in
variable [Category* C]

/--
warning: type of variable contains universe metavariable! Category.{_, u_1} C

Note: This linter can be disabled with `set_option linter.universeMVarInVariable false`
-/
#guard_msgs in
variable [Category C] in example (c : C) : C := c
