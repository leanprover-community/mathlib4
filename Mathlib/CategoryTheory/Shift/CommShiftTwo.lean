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

class Shift₂Data (D : Type*) [Category D] (M : Type*) [AddCommMonoid M] [HasShift D M] where
  z (D) (m₁ m₂ : M) : (CatCenter D)ˣ
  -- TODO: add axioms...

variable [Shift₂Data D M]

/-def twistShiftData : TwistShiftData (PullbackShift D (.sum M)) (M × M) := sorry

abbrev TwistShift₂ : Type _ := TwistShift (twistShiftData D M)

noncomputable def twistShift₂Iso (m₁ m₂ m : M) (hm : m₁ + m₂ = m) :
    shiftFunctor (TwistShift₂ D M) (m₁, m₂) ≅
      shiftFunctor D m :=
  eqToIso (by aesop)-/

end

/-namespace Functor

variable (F : C₁ ⥤ C₂ ⥤ D) (M : Type*) [AddCommMonoid M]
  [HasShift C₁ M] [HasShift C₂ M] [HasShift D M] [Shift₂Data D M]

abbrev uncurryToTwistShift : C₁ × C₂ ⥤ TwistShift₂ D M := uncurry.obj F

abbrev CommShift₂' := (F.uncurryToTwistShift M).CommShift (M × M)

class CommShift₂ where
  commShiftObj (X₁ : C₁) : (F.obj X₁).CommShift M := by infer_instance
  commShiftFlipObj (X₂ : C₂) : (F.flip.obj X₂).CommShift M := by infer_instance
  commShift_map {X₁ Y₁ : C₁} (f : X₁ ⟶ Y₁) : NatTrans.CommShift (F.map f) M := by infer_instance
  commShift_flip_map {X₂ Y₂ : C₂} (f : X₂ ⟶ Y₂) : NatTrans.CommShift (F.flip.map f) M
    := by infer_instance
  compatibility (X₁ : C₁) (X₂ : C₂) (m₁ m₂ : M) :
    ((F.flip.obj (X₂⟦m₂⟧)).commShiftIso m₁).hom.app X₁ ≫
      (((F.obj X₁).commShiftIso m₂).hom.app X₂)⟦m₁⟧' =
        Shift₂Data.z D m₁ m₂ •
          (((F.obj (X₁⟦m₁⟧)).commShiftIso m₂).hom.app X₂) ≫
            (((F.flip.obj X₂).commShiftIso m₁).hom.app (X₁))⟦m₂⟧' ≫
            (shiftFunctorComm D m₁ m₂).hom.app ((F.obj X₁).obj X₂)

namespace CommShift₂

attribute [instance] commShiftObj commShiftFlipObj commShift_map commShift_flip_map

end CommShift₂

section

variable [F.CommShift₂ M] {M}

@[simps!]
def commShift₂Iso' (m₁ m₂ m : M) (h : m₁ + m₂ = m) :
    (((whiskeringLeft₂ _).obj (shiftFunctor C₁ m₁)).obj (shiftFunctor C₂ m₂)).obj F ≅
      ((postcompose₂).obj (shiftFunctor D m)).obj F :=
  NatIso.ofComponents
    (fun X₁ ↦ NatIso.ofComponents
      (fun X₂ ↦
        ((F.obj (X₁⟦m₁⟧)).commShiftIso m₂).app X₂ ≪≫
          (shiftFunctor D m₂).mapIso (((F.flip.obj X₂).commShiftIso m₁).app X₁) ≪≫
          (shiftFunctorAdd' D m₁ m₂ m h).symm.app _) (fun {X₂ Y₂} f ↦ by
            have h₁ := (shiftFunctorAdd' D m₁ m₂ m h).inv.naturality ((F.obj X₁).map f)
            have h₂ := NatTrans.shift_app_comm (F.flip.map f) m₁ X₁
            dsimp at h₁ h₂ ⊢
            simp only [commShiftIso_hom_naturality_assoc, Category.assoc,
              comp_obj, ← h₁, ← Functor.map_comp_assoc, h₂])) (by
      rintro X₁ Y₁ f
      ext X₂
      have h₁ := (shiftFunctorAdd' D m₁ m₂ m h).inv.naturality ((F.map f).app X₂)
      have h₂ := NatTrans.shift_app_comm (F.map (f⟦m₁⟧')) m₂ X₂
      have h₃ := (F.flip.obj X₂).commShiftIso_hom_naturality f m₁
      dsimp at h₁ h₂ h₃ ⊢
      simp only [Category.assoc, ← h₁, ← reassoc_of% h₂, ← Functor.map_comp_assoc, h₃])

end

namespace commshift₂'OfCommShift₂

variable {M} [F.CommShift₂ M]

noncomputable def iso (m₁ m₂ : M) :
    shiftFunctor (C₁ × C₂) (m₁, m₂) ⋙ uncurry.obj F ≅
      uncurry.obj F ⋙ shiftFunctor D (m₁ + m₂) :=
  currying.functor.mapIso (F.commShift₂Iso' m₁ m₂ _ rfl) ≪≫
    NatIso.ofComponents (fun _ ↦ Iso.refl _)

lemma iso_hom_app (m₁ m₂ : M) (X₁ : C₁) (X₂ : C₂) :
    (iso F m₁ m₂).hom.app (X₁, X₂) =
    ((F.obj (X₁⟦m₁⟧)).commShiftIso m₂).hom.app X₂ ≫
      (((F.flip.obj X₂).commShiftIso m₁).hom.app X₁)⟦m₂⟧' ≫
    (shiftFunctorAdd D m₁ m₂).inv.app _:= by
  simp [iso, shiftFunctorAdd'_eq_shiftFunctorAdd]

end commshift₂'OfCommShift₂

open commshift₂'OfCommShift₂ in
noncomputable def commshift₂'OfCommShift₂ [F.CommShift₂ M] :
    F.CommShift₂' M where
  iso m := iso F m.1 m.2 ≪≫ isoWhiskerLeft _ ((twistShift₂Iso D M m.1 m.2 _ rfl).symm)
  zero := by
    ext ⟨X₁, X₂⟩
    rw [CommShift.isoZero_hom_app]
    dsimp
    simp [iso_hom_app (D := D)]
    sorry
  add m n := by
    ext ⟨X₁, X₂⟩
    dsimp
    simp [iso_hom_app (D := D)]
    sorry

end Functor-/

end CategoryTheory
