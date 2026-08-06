import Mathlib.Tactic.Linter.UniverseMVar
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Tactic.CategoryTheory.CategoryStar

set_option linter.universeMVarInVariable true

universe v u

open CategoryTheory

variable (n m : Nat) (m : Nat) (C : Type*)
variable [Category* C]

