/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.HomotopyCategory.Shift

/-!
# Compatibilities of bifunctors acting on cochain complexes and shifts

-/

open CategoryTheory Category Limits

variable {C₁ C₂ D : Type*} [Category C₁] [Category C₂] [Category D]

namespace CochainComplex

section

variable [HasZeroMorphisms C₁] [Preadditive C₂] [Preadditive D]
  (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms]
  [∀ (X₁ : C₁), (F.obj X₁).Additive]
  [∀ (K₁ : CochainComplex C₁ ℤ) (K₂ : CochainComplex C₂ ℤ), HasMapBifunctor K₁ K₂ F]

noncomputable instance (K₁ : CochainComplex C₁ ℤ) :
    (F.bifunctorMapCochainComplex.obj K₁).CommShift ℤ where
  iso y := NatIso.ofComponents (fun K₂ ↦ mapBifunctorShift₂Iso K₁ K₂ F y)
  zero := by ext : 3; simp [mapBifunctorShift₂Iso_hom_zero]
  add _ _ := by ext : 3; simp [mapBifunctorShift₂Iso_hom_add]

lemma bifunctorMapCochainComplex_obj_commShiftIso_hom_app
    (K₁ : CochainComplex C₁ ℤ) (K₂ : CochainComplex C₂ ℤ) (y : ℤ) :
    ((F.bifunctorMapCochainComplex.obj K₁).commShiftIso y).hom.app K₂ =
      (mapBifunctorShift₂Iso K₁ K₂ F y).hom := rfl

lemma bifunctorMapCochainComplex_obj_commShiftIso_inv_app
    (K₁ : CochainComplex C₁ ℤ) (K₂ : CochainComplex C₂ ℤ) (y : ℤ) :
    ((F.bifunctorMapCochainComplex.obj K₁).commShiftIso y).inv.app K₂ =
      (mapBifunctorShift₂Iso K₁ K₂ F y).inv := rfl

end

section

variable [Preadditive C₁] [HasZeroMorphisms C₂] [Preadditive D]
  (F : C₁ ⥤ C₂ ⥤ D) [F.Additive]
  [∀ (X₁ : C₁), (F.obj X₁).PreservesZeroMorphisms]
  [∀ (K₁ : CochainComplex C₁ ℤ) (K₂ : CochainComplex C₂ ℤ), HasMapBifunctor K₁ K₂ F]

noncomputable instance (K₂ : CochainComplex C₂ ℤ) :
    (F.bifunctorMapCochainComplex.flip.obj K₂).CommShift ℤ where
  iso x := NatIso.ofComponents (fun K₁ ↦ mapBifunctorShift₁Iso K₁ K₂ F x)
  zero := by ext : 3; simp [mapBifunctorShift₁Iso_hom_zero]
  add x x' := by ext : 3; simp [mapBifunctorShift₁Iso_hom_add]

lemma bifunctorMapCochainComplex_flip_obj_commShiftIso_hom_app
    (K₁ : CochainComplex C₁ ℤ) (K₂ : CochainComplex C₂ ℤ) (x : ℤ) :
    ((F.bifunctorMapCochainComplex.flip.obj K₂).commShiftIso x).hom.app K₁ =
      (mapBifunctorShift₁Iso K₁ K₂ F x).hom := rfl

lemma bifunctorMapCochainComplex_flip_obj_commShiftIso_inv_app
    (K₁ : CochainComplex C₁ ℤ) (K₂ : CochainComplex C₂ ℤ) (x : ℤ) :
    ((F.bifunctorMapCochainComplex.flip.obj K₂).commShiftIso x).inv.app K₁ =
      (mapBifunctorShift₁Iso K₁ K₂ F x).inv := rfl

end

end CochainComplex
