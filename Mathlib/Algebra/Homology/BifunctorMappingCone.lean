/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.Bifunctor
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone

/-!
# Action of bifunctor on mapping cones
-/

open CategoryTheory Limits HomologicalComplex

namespace CochainComplex

variable
  {C₁ C₂ D : Type*} [Category C₁] [Category C₂] [Category D]
  [Preadditive C₁] [HasZeroMorphisms C₂]
  {K₁ L₁ : CochainComplex C₁ ℤ} (φ : K₁ ⟶ L₁) (K₂ : CochainComplex C₂ ℤ) [Preadditive D]
  (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms]
  [∀ (X₁ : C₁), (F.obj X₁).PreservesZeroMorphisms]
  [HasMapBifunctor K₁ K₂ F (ComplexShape.up ℤ)]
  [HasMapBifunctor L₁ K₂ F (ComplexShape.up ℤ)]
  [HasHomotopyCofiber φ]
  [HasMapBifunctor (mappingCone φ) K₂ F (ComplexShape.up ℤ)]
  [HasHomotopyCofiber (mapBifunctorMap φ (𝟙 K₂) F (.up ℤ))]

open HomComplex

/-noncomputable def mapBifunctorMappingCone₁Iso :
    mapBifunctor (mappingCone φ) K₂ F (.up ℤ) ≅
      mappingCone (mapBifunctorMap φ (𝟙 K₂) F (.up ℤ)) :=
  sorry-/

end CochainComplex
