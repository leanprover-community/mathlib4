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

abbrev Shift₂Data' : Type _ :=
  TwistShiftData (PullbackShift D (.sum M)) (M × M)

structure Shift₂Data where
  z (m₁ m₂ : M) : (CatCenter D)ˣ
  -- TODO: add axioms...

end

namespace Functor

variable (F : C₁ ⥤ C₂ ⥤ D) {M : Type*} [AddCommMonoid M]
  [HasShift C₁ M] [HasShift C₂ M] [HasShift D M]
  (t' : Shift₂Data' D M)

abbrev uncurryToTwistShift : C₁ × C₂ ⥤ TwistShift t' := uncurry.obj F

abbrev CommShift₂' := (F.uncurryToTwistShift t').CommShift (M × M)

variable (t : Shift₂Data D M)

class CommShift₂ where
  commShiftObj (X₁ : C₁) : (F.obj X₁).CommShift M
  commShiftFlipObj (X₂ : C₂) : (F.flip.obj X₂).CommShift M
  commShift_map {X₁ Y₁ : C₁} (f : X₁ ⟶ Y₁) : NatTrans.CommShift (F.map f) M
  commShift_flip_map {X₂ Y₂ : C₂} (f : X₂ ⟶ Y₂) : NatTrans.CommShift (F.flip.map f) M
  compatibility (X₁ : C₁) (X₂ : C₂) (m₁ m₂ : M) :
    ((F.flip.obj (X₂⟦m₂⟧)).commShiftIso m₁).hom.app X₁ ≫
      (((F.obj X₁).commShiftIso m₂).hom.app X₂)⟦m₁⟧' =
        t.z m₁ m₂ •
          (((F.obj (X₁⟦m₁⟧)).commShiftIso m₂).hom.app X₂) ≫
            (((F.flip.obj X₂).commShiftIso m₁).hom.app (X₁))⟦m₂⟧' ≫
            (shiftFunctorComm D m₁ m₂).hom.app ((F.obj X₁).obj X₂)

end Functor

end CategoryTheory
