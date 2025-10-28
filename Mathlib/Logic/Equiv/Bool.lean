/-
Copyright (c) 2025 Emily Riehl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Emily Riehl, Wrenna Robson
-/
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Function.Basic

/-!
# Equivalences involving `Bool`

This file shows that `not : Bool → Bool` is an equivalence and derives some consequences
-/

/-- The boolean negation function `not : Bool → Bool` is an involution and thus an equivalence. -/
@[simps!]
def Equiv.boolNot : Equiv.Perm Bool := Bool.involutive_not.toPerm

namespace Bool

open Function

theorem not_bijective : Bijective not := Equiv.boolNot.bijective
theorem not_injective : Injective not := Equiv.boolNot.injective
theorem not_surjective : Surjective not :=  Equiv.boolNot.surjective

theorem not_leftInverse : LeftInverse not not := not_not
theorem not_rightInverse : RightInverse not not := not_not

theorem not_HasLeftInverse : HasLeftInverse not := ⟨not, not_leftInverse⟩
theorem not_HasRightInverse : HasRightInverse not := ⟨not, not_rightInverse⟩

end Bool
