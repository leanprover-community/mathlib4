/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-!
# Functors between homotopy categories which preserves quasi-isomorphisms

-/

open CategoryTheory Limits ZeroObject Pretriangulated

namespace HomotopyCategory

variable {C₁ C₂ : Type*} [Category C₁] [Category C₂] [Abelian C₁] [Abelian C₂]
  (F : HomotopyCategory C₁ (.up ℤ) ⥤ HomotopyCategory C₂ (.up ℤ))
  [F.CommShift ℤ] [F.IsTriangulated]

lemma preservesQuasiIso_iff_preserves_acyclic :
    preservesQuasiIso F ↔
      subcategoryAcyclic C₁ ≤ (subcategoryAcyclic C₂).inverseImage F := by
  constructor
  · intro hF K hK
    have hf : quasiIso _ _ (0 : 0 ⟶ K) := by
      rw [quasiIso_eq_subcategoryAcyclic_trW, ObjectProperty.trW_iff]
      refine ⟨K, 𝟙 K, 0, isomorphic_distinguished _
        (inv_rot_of_distTriang _ (contractible_distinguished K)) _ ?_, hK⟩
      exact Triangle.isoMk _ _ ((Functor.mapZeroObject _).symm)
        (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simp)
    replace hf := hF _ hf
    simp only [MorphismProperty.inverseImage_iff,
      quasiIso_eq_subcategoryAcyclic_trW] at hf
    rw [ObjectProperty.trW_iff] at hf
    obtain ⟨Z, g, h, hT, hZ⟩ := hf
    simp only [ObjectProperty.prop_inverseImage_iff]
    have := (subcategoryAcyclic C₂).ext_of_isTriangulatedClosed₂ _ hT
    exact (subcategoryAcyclic C₂).ext_of_isTriangulatedClosed₂ _ hT
      (ObjectProperty.prop_of_isZero _ (F.map_isZero (isZero_zero _))) hZ
  · intro hF K L f hf
    simp only [MorphismProperty.inverseImage_iff,
      quasiIso_eq_subcategoryAcyclic_trW] at hf ⊢
    rw [ObjectProperty.trW_iff] at hf
    obtain ⟨Z, g, h, hT, hZ⟩ := hf
    exact ObjectProperty.trW.mk _ (F.map_distinguished _ hT) (hF _ hZ)

end HomotopyCategory
