/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.GradedObject.Colimits
import Mathlib.Algebra.Homology.Bifunctor
import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-!
# Commutation with colimits of bifunctors on homological complexes
-/

open CategoryTheory Limits HomologicalComplex

variable {C₁ C₂ D : Type*} [Category C₁] [Category C₂] [Category D]

namespace CategoryTheory

namespace Functor

variable [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [Preadditive D]
  (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms] [∀ X₁, (F.obj X₁).PreservesZeroMorphisms]
  {I₁ I₂ J : Type*} (c₁ : ComplexShape I₁) (c₂ : ComplexShape I₂)
  (c : ComplexShape J) [TotalComplexShape c₁ c₂ c] [DecidableEq J]
  (B : Type*) [Category B] [HasColimitsOfShape B D]
  [∀ (j : J), HasColimitsOfShape (Discrete (ComplexShape.π c₁ c₂ c ⁻¹' {j})) D]

instance (K₁ : HomologicalComplex C₁ c₁) [HasColimitsOfShape B C₂]
    [∀ i₁, PreservesColimitsOfShape B (F.obj (K₁.X i₁))] :
    PreservesColimitsOfShape B ((bifunctorMapHomologicalComplex F c₁ c₂ c).obj K₁) := by
  have e : (bifunctorMapHomologicalComplex F c₁ c₂ c).obj K₁ ⋙ HomologicalComplex.forget _ _ ≅
      HomologicalComplex.forget _ _ ⋙
        (GradedObject.mapBifunctorMap F (ComplexShape.π c₁ c₂ c)).obj K₁.X := Iso.refl _
  have := preservesColimitsOfShape_of_natIso (J := B) e.symm
  exact preservesColimitsOfShape_of_reflects_of_preserves _
    (HomologicalComplex.forget D c)

instance (K₂ : HomologicalComplex C₂ c₂) [HasColimitsOfShape B C₁]
    [∀ i₂, PreservesColimitsOfShape B (F.flip.obj (K₂.X i₂))] :
    PreservesColimitsOfShape B ((bifunctorMapHomologicalComplex F c₁ c₂ c).flip.obj K₂) := by
  have e : (bifunctorMapHomologicalComplex F c₁ c₂ c).flip.obj K₂ ⋙ HomologicalComplex.forget _ _ ≅
      HomologicalComplex.forget _ _ ⋙
        (GradedObject.mapBifunctorMap F (ComplexShape.π c₁ c₂ c)).flip.obj K₂.X := Iso.refl _
  have := preservesColimitsOfShape_of_natIso (J := B) e.symm
  exact preservesColimitsOfShape_of_reflects_of_preserves _
    (HomologicalComplex.forget D c)

end Functor

end CategoryTheory
