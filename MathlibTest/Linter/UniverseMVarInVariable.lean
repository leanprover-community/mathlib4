import Mathlib.Tactic.Linter.UniverseMVar
import Mathlib.CategoryTheory.Yoneda

set_option linter.universeMVarInVariable true

universe v u

open CategoryTheory

variable (n m : Nat) (m : Nat) (C : Type*)
variable [Category* C]

