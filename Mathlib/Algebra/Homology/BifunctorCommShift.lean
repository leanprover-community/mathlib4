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

variable [HasZeroMorphisms C₁] [Preadditive C₂]
  (K₁ : CochainComplex C₁ ℤ) (K₂ : CochainComplex C₂ ℤ) [Preadditive D]
  (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms]
  [∀ (X₁ : C₁), (F.obj X₁).Additive]
  [∀ (K₁ : CochainComplex C₁ ℤ) (K₂ : CochainComplex C₂ ℤ), HasMapBifunctor K₁ K₂ F]

noncomputable example (K₁ : CochainComplex C₁ ℤ) :
    (F.bifunctorMapCochainComplex.obj K₁).CommShift ℤ where
  iso y := NatIso.ofComponents (fun K₂ ↦ mapBifunctorShift₂Iso K₁ K₂ F y)
  zero := by ext : 3; simp [mapBifunctorShift₂Iso_hom_zero]
  add a b := by ext K₂ : 3; simp [mapBifunctorShift₂Iso_hom_add]

end

end CochainComplex
