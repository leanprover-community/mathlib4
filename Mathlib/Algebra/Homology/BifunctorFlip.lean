/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.Algebra.Homology.TotalComplexSymmetry

/-!
# Action of the flip of a bifunctor on homological complexes

Given `K₁ : HomologicalComplex C₁ c₁`, `K₂ : HomologicalComplex C₂ c₂`,
a bifunctor `F : C₁ ⥤ C₂ ⥤ D`, and a complex shape `c` with
`[TotalComplexShape c₁ c₂ c]` and `[TotalComplexShape c₂ c₁ c]`, we define
an isomorphism `mapBifunctor K₂ K₁ F.flip c ≅ mapBifunctor K₁ K₂ F c`
under the additional assumption `[TotalComplexShapeSymmetry c₁ c₂ c]`.

-/

@[expose] public section

open CategoryTheory Limits

variable {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]

namespace HomologicalComplex

variable {I₁ I₂ J : Type*} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
  [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [Preadditive D]
  (K₁ L₁ : HomologicalComplex C₁ c₁) (φ₁ : K₁ ⟶ L₁)
  (K₂ L₂ : HomologicalComplex C₂ c₂) (φ₂ : K₂ ⟶ L₂)
  (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms] [∀ X₁, (F.obj X₁).PreservesZeroMorphisms]
  (c : ComplexShape J) [TotalComplexShape c₁ c₂ c] [TotalComplexShape c₂ c₁ c]
  [TotalComplexShapeSymmetry c₁ c₂ c]

lemma hasMapBifunctor_flip_iff :
    HasMapBifunctor K₂ K₁ F.flip c ↔ HasMapBifunctor K₁ K₂ F c :=
  (((F.mapBifunctorHomologicalComplex c₁ c₂).obj K₁).obj K₂).flip_hasTotal_iff c

variable [DecidableEq J] [HasMapBifunctor K₁ K₂ F c] [HasMapBifunctor L₁ L₂ F c]

instance : HasMapBifunctor K₂ K₁ F.flip c := by
  rw [hasMapBifunctor_flip_iff]
  infer_instance

/-- The canonical isomorphism `mapBifunctor K₂ K₁ F.flip c ≅ mapBifunctor K₁ K₂ F c`. -/
noncomputable def mapBifunctorFlipIso :
    mapBifunctor K₂ K₁ F.flip c ≅ mapBifunctor K₁ K₂ F c :=
  (((F.mapBifunctorHomologicalComplex c₁ c₂).obj K₁).obj K₂).totalFlipIso c

@[reassoc (attr := simp)]
lemma ι_mapBifunctorFlipIso_hom (i₁ : I₁) (i₂ : I₂) (j : J) (hj : c₂.π c₁ c (i₂, i₁) = j) :
    ιMapBifunctor K₂ K₁ F.flip c i₂ i₁ j hj ≫ (mapBifunctorFlipIso K₁ K₂ F c).hom.f j =
      c₁.σ c₂ c i₁ i₂ • ιMapBifunctor K₁ K₂ F c i₁ i₂ j
        (by rw [← ComplexShape.π_symm c₁ c₂ c i₁ i₂, hj]) :=
  HomologicalComplex₂.ιTotal_totalFlipIso_f_hom
    (((F.mapBifunctorHomologicalComplex c₁ c₂).obj K₁).obj K₂) c i₁ i₂ j hj

@[reassoc (attr := simp)]
lemma ι_mapBifunctorFlipIso_inv (i₁ : I₁) (i₂ : I₂) (j : J) (hj : c₁.π c₂ c (i₁, i₂) = j) :
    ιMapBifunctor K₁ K₂ F c i₁ i₂ j hj ≫ (mapBifunctorFlipIso K₁ K₂ F c).inv.f j =
      c₁.σ c₂ c i₁ i₂ • ιMapBifunctor K₂ K₁ F.flip c i₂ i₁ j
        (by rw [ComplexShape.π_symm c₁ c₂ c i₁ i₂, hj]) :=
  HomologicalComplex₂.ιTotal_totalFlipIso_f_inv
    (((F.mapBifunctorHomologicalComplex c₁ c₂).obj K₁).obj K₂) c i₁ i₂ j hj

lemma mapBifunctorFlipIso_flip
    [TotalComplexShapeSymmetry c₂ c₁ c] [TotalComplexShapeSymmetrySymmetry c₁ c₂ c] :
    mapBifunctorFlipIso K₂ K₁ F.flip c = (mapBifunctorFlipIso K₁ K₂ F c).symm :=
  (((F.mapBifunctorHomologicalComplex c₁ c₂).obj K₁).obj K₂).flip_totalFlipIso c

variable {K₁ K₂ L₁ L₂} in
@[reassoc (attr := simp)]
lemma mapBifunctorFlipIso_hom_naturality :
      mapBifunctorMap φ₂ φ₁ F.flip c ≫ (mapBifunctorFlipIso L₁ L₂ F c).hom =
    (mapBifunctorFlipIso K₁ K₂ F c).hom ≫ mapBifunctorMap φ₁ φ₂ F c := by
  cat_disch

end HomologicalComplex
