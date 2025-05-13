/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.BifunctorCommShift
import Mathlib.Algebra.Homology.BifunctorMappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated

/-!
# Bifunctors acting of the homotopy category are triangulated in each variable

-/

open CategoryTheory Category Limits Pretriangulated

variable {C₁ C₂ D : Type*} [Category C₁] [Category C₂] [Category D]

namespace CochainComplex

open HomComplex

section

variable [Preadditive C₁] [HasBinaryBiproducts C₁]
  [HasZeroMorphisms C₂] [Preadditive D] [HasBinaryBiproducts D]
  (F : C₁ ⥤ C₂ ⥤ D) [F.Additive]
  [∀ (X₁ : C₁), (F.obj X₁).PreservesZeroMorphisms]
  [∀ (K₁ : CochainComplex C₁ ℤ) (K₂ : CochainComplex C₂ ℤ), HasMapBifunctor K₁ K₂ F]

noncomputable def bifunctorMapCochainComplexFlipObjMapMappingConeTriangleIso
    {K₁ L₁ : CochainComplex C₁ ℤ} (f : K₁ ⟶ L₁) (K₂ : CochainComplex C₂ ℤ) :
    (F.bifunctorMapCochainComplex.flip.obj K₂).mapTriangle.obj (mappingCone.triangle f) ≅
      mappingCone.triangle (HomologicalComplex.mapBifunctorMap f (𝟙 K₂) F (.up ℤ)) :=
  Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (mapBifunctorMappingCone₁Iso f K₂ F)
    (by simp) (by simp) (by
      dsimp
      ext n p q hpq
      dsimp at hpq
      simp [mappingCone.triangle, Cochain.rightShift_v _ _ _ (zero_add 1) p p (add_zero p) _ rfl,
        Cochain.rightShift_v _ _ _ (zero_add 1) n n (add_zero n) _ rfl,
        mapBifunctorMappingCone₁Iso.hom,
        mapBifunctorMappingCone₁Iso.ι_p₁₀_v _ _ _ p q n hpq _ rfl _ rfl,
        bifunctorMapCochainComplex_flip_obj_commShiftIso_hom_app,
        mapBifunctorShift₁Iso, HomologicalComplex₂.totalShift₁Iso,
        HomologicalComplex₂.totalShift₁XIso])

end

section

variable [HasZeroMorphisms C₁]
  [Preadditive C₂] [HasBinaryBiproducts C₂] [Preadditive D] [HasBinaryBiproducts D]
  (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms]
  [∀ (X₁ : C₁), (F.obj X₁).Additive]
  [∀ (K₁ : CochainComplex C₁ ℤ) (K₂ : CochainComplex C₂ ℤ), HasMapBifunctor K₁ K₂ F]

noncomputable def bifunctorMapCochainComplexObjMapMappingConeTriangleIso
    (K₁ : CochainComplex C₁ ℤ) {K₂ L₂ : CochainComplex C₂ ℤ} (f : K₂ ⟶ L₂) :
    (F.bifunctorMapCochainComplex.obj K₁).mapTriangle.obj (mappingCone.triangle f) ≅
      mappingCone.triangle (HomologicalComplex.mapBifunctorMap (𝟙 K₁) f F (.up ℤ)) :=
  Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (mapBifunctorMappingCone₂Iso K₁ f F)
    (by simp) (by simp) (by
      dsimp
      ext n p q hpq
      dsimp at hpq
      simp [mappingCone.triangle, Cochain.rightShift_v _ _ _ (zero_add 1) q q (add_zero q) _ rfl,
        Cochain.rightShift_v _ _ _ (zero_add 1) n n (add_zero n) _ rfl,
        mapBifunctorMappingCone₂Iso.hom,
        mapBifunctorMappingCone₂Iso.ι_p₁₀_v _ _ _ p q n hpq _ rfl _ rfl,
        bifunctorMapCochainComplex_obj_commShiftIso_hom_app,
        mapBifunctorShift₂Iso, HomologicalComplex₂.totalShift₂Iso,
        HomologicalComplex₂.totalShift₂XIso])

end

end CochainComplex
