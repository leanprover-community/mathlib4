/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Shift.CommShiftProd
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

variable {C C₁ C₂ D : Type*}
  [Category C] [Category C₁] [Category C₂] [Category D]

section

variable (D) (M : Type*)
  [AddCommMonoid M] [HasShift C₁ M] [HasShift C₂ M] [HasShift D M]

structure CommShift₂Setup where
  twistShiftData : TwistShiftData (PullbackShift D (.sum M)) (M × M)
  ε (m n : M) : (CatCenter D)ˣ

end

namespace Functor

class CommShift₂ (G : C₁ ⥤ C₂ ⥤ D) {M : Type*}
    [AddCommMonoid M] [HasShift C₁ M] [HasShift C₂ M] [HasShift D M] (h : CommShift₂Setup D M) where
  commShiftObj (X₁ : C₁) : (G.obj X₁).CommShift M
  commShift_map {X₁ Y₁ : C₁} (f : X₁ ⟶ Y₁) : NatTrans.CommShift (G.map f) M
  commShiftFlipObj (X₂ : C₂) : (G.flip.obj X₂).CommShift M
  commShift_flip_map {X₂ Y₂ : C₂} (g : X₂ ⟶ Y₂) : NatTrans.CommShift (G.flip.map g) M
  comm (G h) (X₁ : C₁) (X₂ : C₂) (m n : M) :
      ((G.obj (X₁⟦m⟧)).commShiftIso n).hom.app X₂ ≫
          (((G.flip.obj X₂).commShiftIso m).hom.app X₁)⟦n⟧' =
        ((G.flip.obj (X₂⟦n⟧)).commShiftIso m).hom.app X₁ ≫
          (((G.obj X₁).commShiftIso n).hom.app X₂)⟦m⟧' ≫
          (shiftComm ((G.obj X₁).obj X₂) m n).inv ≫ (h.ε m n).val.app _

namespace CommShift₂

attribute [instance] commShiftObj commShiftFlipObj
  commShift_map commShift_flip_map

end CommShift₂

end Functor

variable {M : Type*} [AddCommMonoid M] [HasShift C₁ M] [HasShift C₂ M] [HasShift D M]
variable (h : CommShift₂Setup D M)

namespace CommShift₂Setup

protected def Category (h : CommShift₂Setup D M) := TwistShift h.twistShiftData

instance : Category h.Category := inferInstanceAs (Category (TwistShift h.twistShiftData))

noncomputable instance : HasShift h.Category (M × M) :=
  inferInstanceAs (HasShift (TwistShift h.twistShiftData) (M × M))

-- variable (G : C₁ × C₂ ⥤ h.Category) [G.CommShift (M × M)]
-- should be essentially equivalent to
-- variable (F : C₁ ⥤ C₂ ⥤ D) [F.CommShift₂ h]

noncomputable def shiftIso (m n p : M) (hp : m + n = p) :
    shiftFunctor h.Category (m, n) ≅ shiftFunctor D p :=
  pullbackShiftIso _ _ _ _ hp.symm

lemma shiftFunctorZero_inv_app (X : h.Category) :
    (shiftFunctorZero _ (M × M)).inv.app X =
      (shiftFunctorZero D M).inv.app X ≫ (h.shiftIso 0 0 0 (add_zero 0)).inv.app X :=
  pullbackShiftFunctorZero_inv_app ..

variable (F : C₁ ⥤ C₂ ⥤ D) [F.CommShift₂ h]

abbrev uncurry : C₁ × C₂ ⥤ h.Category := CategoryTheory.uncurry.obj F

namespace commShiftUncurry

noncomputable def iso₁ (m₁ : M) :
    shiftFunctor (C₁ × C₂) (m₁, (0 : M)) ⋙ h.uncurry F ≅
      h.uncurry F ⋙ shiftFunctor h.Category (m₁, (0 : M)) :=
  fullyFaithfulCurry.preimageIso (NatIso.ofComponents
    (fun X₁ ↦ NatIso.ofComponents (fun X₂ ↦
      (F.obj (X₁⟦m₁⟧)).mapIso ((shiftFunctorZero C₂ M).app X₂) ≪≫
        ((F.flip.obj X₂).commShiftIso m₁).app X₁ ≪≫
        (h.shiftIso m₁ 0 m₁ (add_zero m₁)).symm.app _)
      (fun {X₂ Y₂} f ↦ by
        have := NatTrans.shift_app_comm (F.flip.map f) m₁ X₁
        dsimp at this ⊢
        simp only [Functor.map_id, NatTrans.id_app, Category.id_comp,
          Category.assoc, ← NatTrans.naturality, reassoc_of% this]
        simp [-Functor.map_comp, ← Functor.map_comp_assoc]))
    (fun {X₁ Y₁} f ↦ by
      ext X₂
      have := (F.flip.obj X₂).commShiftIso_hom_naturality f m₁
      dsimp at this ⊢
      simp only [Functor.map_id, Category.comp_id, Category.assoc,
        ← NatTrans.naturality, ← NatTrans.naturality_assoc, ← reassoc_of% this]))

@[reassoc]
lemma iso₁_hom_app (X₁ : C₁) (X₂ : C₂) (m₁ : M) :
    (iso₁ h F m₁).hom.app (X₁, X₂) =
    (F.obj ((shiftFunctor C₁ m₁).obj X₁)).map ((shiftFunctorZero C₂ M).hom.app X₂) ≫
    ((F.flip.obj X₂).commShiftIso m₁).hom.app X₁ ≫
      (h.shiftIso m₁ 0 m₁ (add_zero m₁)).inv.app ((F.obj X₁).obj X₂) := by
  simp [iso₁, fullyFaithfulCurry, Equivalence.fullyFaithfulInverse]

variable (M) in
@[simp]
lemma iso₁_zero : iso₁ h F 0 = Functor.CommShift.isoZero _ _ := by
  ext ⟨X₁, X₂⟩
  simp [iso₁_hom_app, shiftFunctorZero_inv_app, Functor.commShiftIso_zero]

noncomputable def iso₂ (m₂ : M) :
    shiftFunctor (C₁ × C₂) ((0 : M), m₂) ⋙ h.uncurry F ≅
      h.uncurry F ⋙ shiftFunctor h.Category ((0 : M), m₂) :=
  fullyFaithfulCurry.preimageIso (NatIso.ofComponents
    (fun X₁ ↦ NatIso.ofComponents (fun X₂ ↦
      (F.mapIso ((shiftFunctorZero C₁ M).app X₁)).app (X₂⟦m₂⟧) ≪≫
        ((F.obj X₁).commShiftIso m₂).app X₂ ≪≫
        (h.shiftIso 0 m₂ m₂ (zero_add m₂)).symm.app ((F.obj X₁).obj X₂))
      (fun {X₂ Y₂} f ↦ by simp))
    (fun {X₁ Y₁} f ↦ by
      ext X₂
      have := congr_app (F.congr_map ((shiftFunctorZero C₁ M).hom.naturality f)) (X₂⟦m₂⟧)
      simp only [Functor.map_comp] at this
      dsimp at this ⊢
      simp only [Functor.map_id, Category.comp_id, Category.assoc, ← NatTrans.naturality]
      rw [NatTrans.shift_app_comm_assoc (F.map f) m₂ X₂, reassoc_of% this]))

@[reassoc]
lemma iso₂_hom_app (X₁ : C₁) (X₂ : C₂) (m₂ : M) :
    (iso₂ h F m₂).hom.app (X₁, X₂) =
      (F.map ((shiftFunctorZero C₁ M).hom.app X₁)).app (X₂⟦m₂⟧) ≫
        ((F.obj X₁).commShiftIso m₂).hom.app X₂ ≫
        (h.shiftIso 0 m₂ m₂ (zero_add m₂)).inv.app ((F.obj X₁).obj X₂) := by
  simp [iso₂, fullyFaithfulCurry, Equivalence.fullyFaithfulInverse]

variable (M) in
@[simp]
lemma iso₂_zero : iso₂ h F 0 = Functor.CommShift.isoZero _ _ := by
  ext ⟨X₁, X₂⟩
  simp [iso₂_hom_app, shiftFunctorZero_inv_app, Functor.commShiftIso_zero]

end commShiftUncurry

open commShiftUncurry in
noncomputable instance commShiftUncurry : (h.uncurry F).CommShift (M × M) :=
  Functor.CommShift.mkProd (iso₁ h F) (iso₂ h F) (by simp) (by simp) sorry sorry
    (fun m₁ m₂ ↦ by
      ext ⟨X₁, X₂⟩
      simp [shiftFunctorAdd'_add_zero_hom_app, shiftFunctorAdd'_zero_add_hom_app,
        iso₁_hom_app, iso₂_hom_app]
      have := Functor.CommShift₂.comm F h X₁ X₂ m₁ m₂
      dsimp at this
      sorry)

end CommShift₂Setup

end CategoryTheory
