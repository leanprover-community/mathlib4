/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.BifunctorCommShift
public import Mathlib.Algebra.Homology.BifunctorMappingCone
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated

/-!
# Bifunctors acting of the homotopy category are triangulated in each variable

-/

@[expose] public section

open CategoryTheory Category Limits Pretriangulated

variable {C₁ C₂ D : Type*} [Category C₁] [Category C₂] [Category D]

namespace CochainComplex

open HomComplex

section

variable [Preadditive C₁] [HasBinaryBiproducts C₁]
  [Preadditive C₂] [HasBinaryBiproducts C₂] [Preadditive D] [HasBinaryBiproducts D]
  (F : C₁ ⥤ C₂ ⥤ D) [F.Additive]
  [∀ (X₁ : C₁), (F.obj X₁).Additive]
  [∀ (K₁ : CochainComplex C₁ ℤ) (K₂ : CochainComplex C₂ ℤ), HasMapBifunctor K₁ K₂ F]

set_option backward.isDefEq.respectTransparency false in
noncomputable def map₂CochainComplexFlipObjMapMappingConeTriangleIso
    {K₁ L₁ : CochainComplex C₁ ℤ} (f : K₁ ⟶ L₁) (K₂ : CochainComplex C₂ ℤ) :
    (F.map₂CochainComplex.flip.obj K₂).mapTriangle.obj (mappingCone.triangle f) ≅
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
        map₂CochainComplex_flip_obj_commShiftIso_hom_app,
        mapBifunctorShift₁Iso, HomologicalComplex₂.totalShift₁Iso,
        HomologicalComplex₂.totalShift₁XIso])

set_option backward.isDefEq.respectTransparency false in
noncomputable def bifunctorMapCochainComplexObjMapMappingConeTriangleIso
    (K₁ : CochainComplex C₁ ℤ) {K₂ L₂ : CochainComplex C₂ ℤ} (f : K₂ ⟶ L₂) :
    (F.map₂CochainComplex.obj K₁).mapTriangle.obj (mappingCone.triangle f) ≅
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
        map₂CochainComplex_obj_commShiftIso_hom_app,
        mapBifunctorShift₂Iso, HomologicalComplex₂.totalShift₂Iso,
        HomologicalComplex₂.totalShift₂XIso])

end

end CochainComplex

namespace HomotopyCategory

section

variable [Preadditive C₁] [Preadditive C₂] [Preadditive D] [HasBinaryBiproducts D]
  [HasZeroObject D]
   (F : C₁ ⥤ C₂ ⥤ D) [F.Additive]
  [∀ (X₁ : C₁), (F.obj X₁).Additive]
  [∀ (K₁ : CochainComplex C₁ ℤ) (K₂ : CochainComplex C₂ ℤ), CochainComplex.HasMapBifunctor K₁ K₂ F]

instance (K₁ : HomotopyCategory C₁ (.up ℤ)) [HasZeroObject C₂] [HasBinaryBiproducts C₂] :
    ((F.bifunctorMapHomotopyCategory (.up ℤ) (.up ℤ) (.up ℤ)).obj K₁).IsTriangulated := by
  obtain ⟨K₁, rfl⟩ := K₁.quotient_obj_surjective
  rw [functor_from_isTriangulated_iff]
  intro K₂ L₂ f
  exact isomorphic_distinguished _ (mappingCone_triangleh_distinguished
    (HomologicalComplex.mapBifunctorMap (𝟙 K₁) f F (ComplexShape.up ℤ))) _
      ((Functor.mapTriangleCompIso _ _).symm.app _ ≪≫
        (Functor.mapTriangleIso
          (F.quotientCompBifunctorMapHomotopyObjIso (.up ℤ) (.up ℤ) (.up ℤ) K₁)).app _ ≪≫
        (Functor.mapTriangleCompIso _ _).app _ ≪≫ (quotient D (.up ℤ)).mapTriangle.mapIso
        (CochainComplex.bifunctorMapCochainComplexObjMapMappingConeTriangleIso F K₁ f))

instance (K₂ : HomotopyCategory C₂ (.up ℤ)) [HasZeroObject C₁] [HasBinaryBiproducts C₁] :
    ((F.bifunctorMapHomotopyCategory (.up ℤ) (.up ℤ) (.up ℤ)).flip.obj K₂).IsTriangulated := by
  obtain ⟨K₂, rfl⟩ := K₂.quotient_obj_surjective
  rw [functor_from_isTriangulated_iff]
  intro K₁ L₁ f
  exact isomorphic_distinguished _ (mappingCone_triangleh_distinguished
    (HomologicalComplex.mapBifunctorMap f (𝟙 K₂) F (ComplexShape.up ℤ))) _
      ((Functor.mapTriangleCompIso _ _).symm.app _ ≪≫
        (Functor.mapTriangleIso
          (F.quotientCompBifunctorMapHomotopyFlipObjIso (.up ℤ) (.up ℤ) (.up ℤ) K₂)).app _ ≪≫
        (Functor.mapTriangleCompIso _ _).app _  ≪≫ (quotient D (.up ℤ)).mapTriangle.mapIso
        (CochainComplex.map₂CochainComplexFlipObjMapMappingConeTriangleIso F f K₂))

end

end HomotopyCategory
