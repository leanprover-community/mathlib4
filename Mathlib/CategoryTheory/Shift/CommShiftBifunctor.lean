/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.CategoryTheory.Shift.Twist
import Mathlib.CategoryTheory.Shift.Products
import Mathlib.CategoryTheory.Shift.Pullback

/-!
# Bifunctors which commute with shifts

-/

namespace CategoryTheory

open Category

namespace Functor

variable {C₁ C₂ D : Type*} [Category C₁] [Category C₂] [Category D]
  (F : C₁ ⥤ C₂ ⥤ D)
  (A : Type*) [AddCommMonoid A] [HasShift C₁ A] [HasShift C₂ A] [HasShift D A]

variable (D) in
structure CommShift₂Data where
  ε (a b : A) : (CatCenter D)ˣ
  ε_zero_zero : ε 0 0 = 1
  --ε_zero₁ (a : A) : ε a (0 : A) = 1
  --ε_zero₂ (b : A) : ε (0 : A) b = 1
  commutes (a b c : A) : (shiftFunctor D a).CommutesWithCenterElement (ε b c).val :=
    by infer_instance

namespace CommShift₂Data

attribute [simp] ε_zero_zero

variable {A} (t : CommShift₂Data D A)

def twistShiftData :
    TwistShiftData (PullbackShift D (AddMonoidHom.fst A A + AddMonoidHom.snd A A)) (A × A) where
  ε := fun ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ ↦ by
    have := t
    sorry
  zero_add := sorry
  add_zero := sorry
  assoc := sorry
  commutes := sorry

end CommShift₂Data

class PreCommShift₂ where
  commShiftObj (X₁ : C₁) : (F.obj X₁).CommShift A := by infer_instance
  commShiftFlipObj (X₂ : C₂) : (F.flip.obj X₂).CommShift A := by infer_instance
  commShift_map {X₁ Y₁ : C₁} (f : X₁ ⟶ Y₁) :
    NatTrans.CommShift (F.map f) A := by infer_instance
  commShift_flip_map {X₂ Y₂ : C₂} (g : X₂ ⟶ Y₂) :
    NatTrans.CommShift (F.flip.map g) A := by infer_instance

namespace PreCommShift₂

attribute [instance] commShiftObj commShiftFlipObj commShift_map commShift_flip_map

end PreCommShift₂

variable {A}

class CommShift₂ (t : CommShift₂Data D A) extends F.PreCommShift₂ A where
  compatibility (X₁ : C₁) (X₂ : C₂) (x₁ x₂ : A) :
    ((F.flip.obj (X₂⟦x₂⟧)).commShiftIso x₁).hom.app X₁ ≫
      (((F.obj X₁).commShiftIso x₂).hom.app X₂)⟦x₁⟧' =
    (t.ε x₁ x₂).val.app _ ≫ ((F.obj (X₁⟦x₁⟧)).commShiftIso x₂).hom.app X₂ ≫
      (((F.flip.obj X₂).commShiftIso x₁).hom.app X₁)⟦x₂⟧' ≫
      (shiftFunctorComm D x₁ x₂).hom.app ((F.obj X₁).obj X₂)

variable (t : CommShift₂Data D A)

def uncurry₂ToTwistShift : C₁ × C₂ ⥤ t.twistShiftData.toCategory := uncurry.obj F

namespace comShiftUncurry₂ToTwistShift

variable [F.CommShift₂ t]

noncomputable def iso (x₁ x₂ : A) :
    shiftFunctor (C₁ × C₂) (⟨x₁, x₂⟩ : A × A) ⋙ F.uncurry₂ToTwistShift t ≅
      F.uncurry₂ToTwistShift t ⋙ shiftFunctor t.twistShiftData.toCategory (⟨x₁, x₂⟩ : A × A) :=
  fullyFaithfulCurry.preimageIso (NatIso.ofComponents (fun X₁ ↦
    NatIso.ofComponents (fun X₂ ↦
      (CatCenter.unitsMulEquiv (t.ε x₁ x₂)).app ((F.obj (X₁⟦x₁⟧)).obj (X₂⟦x₂⟧)) ≪≫
        ((F.obj (X₁⟦x₁⟧)).commShiftIso x₂).app X₂ ≪≫
        (shiftFunctor D x₂).mapIso (((F.flip.obj X₂).commShiftIso x₁).app X₁) ≪≫
        ((shiftFunctorAdd D x₁ x₂).app ((F.obj X₁).obj X₂)).symm) sorry) (sorry))

@[reassoc (attr := simp)]
lemma iso_hom_app (X₁ : C₁) (X₂ : C₂) (x₁ x₂ : A) :
    (iso F t x₁ x₂).hom.app ⟨X₁, X₂⟩ =
      (t.ε x₁ x₂).val.app _ ≫
        ((F.obj ((shiftFunctor C₁ x₁).obj X₁)).commShiftIso x₂).hom.app X₂ ≫
        (shiftFunctor D x₂).map (((F.flip.obj X₂).commShiftIso x₁).hom.app X₁) ≫
        (shiftFunctorAdd D x₁ x₂).inv.app ((F.obj X₁).obj X₂) :=
          by
  dsimp
  simp [iso, fullyFaithfulCurry, Equivalence.fullyFaithfulFunctor]

lemma iso_zero : iso F t 0 0 = CommShift.isoZero (F.uncurry₂ToTwistShift t) (A × A) := by
  ext ⟨X₁, X₂⟩
  dsimp [uncurry₂ToTwistShift]
  simp [commShiftIso_zero]
  erw [pullbackShiftFunctorZero_inv_app]
  dsimp
  sorry

end comShiftUncurry₂ToTwistShift

variable [F.CommShift₂ t]
open comShiftUncurry₂ToTwistShift in
noncomputable def comShiftUncurry₂ToTwistShift :
    (uncurry₂ToTwistShift F t).CommShift (A × A) where
  iso a := iso F t a.1 a.2
  zero := iso_zero F t
  add := sorry

end Functor

end CategoryTheory
