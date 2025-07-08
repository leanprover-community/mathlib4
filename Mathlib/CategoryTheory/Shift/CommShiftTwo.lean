/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Shift.CommShift
import Mathlib.CategoryTheory.Shift.Prod
import Mathlib.CategoryTheory.Shift.Twist
import Mathlib.CategoryTheory.Shift.Pullback

/-!
# Commutation to shifts of functors in two variables

-/

@[simps]
def AddMonoidHom.sum (M : Type*) [AddCommMonoid M] : M × M →+ M where
  toFun m := m.1 + m.2
  map_zero' := by simp
  map_add' := by
    rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩
    dsimp
    rw [add_assoc, ← add_assoc y₁, add_comm y₁, add_assoc, add_assoc]

namespace CategoryTheory

variable {C₁ C₂ D : Type*} [Category C₁] [Category C₂] [Category D]

section

variable (D) (M : Type*) [AddCommMonoid M] [HasShift D M]

abbrev Shift₂Data : Type _ :=
  TwistShiftData (PullbackShift D (.sum M)) (M × M)

end

namespace Functor

variable (F : C₁ ⥤ C₂ ⥤ D) {M : Type*} [AddCommMonoid M]
  [HasShift C₁ M] [HasShift C₂ M] [HasShift D M]
  (t : Shift₂Data D M)

abbrev uncurryToTwistShift : C₁ × C₂ ⥤ TwistShift t := uncurry.obj F

abbrev CommShift₂' := (F.uncurryToTwistShift t).CommShift (M × M)

end Functor

end CategoryTheory
