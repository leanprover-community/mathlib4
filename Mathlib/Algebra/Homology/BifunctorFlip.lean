/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.BifunctorHomotopy
import Mathlib.Algebra.Homology.TotalComplexSymmetry

open CategoryTheory Limits

variable {C₁ C₂ D : Type*} [Category C₁] [Category C₂] [Category D]



namespace HomologicalComplex

variable {I₁ I₂ J : Type*} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
  [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [Preadditive D]
  (K₁ : HomologicalComplex C₁ c₁) (K₂ : HomologicalComplex C₂ c₂)
  (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms] [∀ X₁, (F.obj X₁).PreservesZeroMorphisms]
  (c : ComplexShape J) [TotalComplexShape c₁ c₂ c]
  /-
#check HomologicalComplex₂.hasTotal_of_iso
instance [HasMapBifunctor K₁ K₂ F c] : HasMapBifunctor K₂ K₁ F.flip c := fun j => by
  sorry

lemma hasMapBifunctor_flip_iff :
    HasMapBifunctor K₂ K₁ F.flip c ↔ HasMapBifunctor K₁ K₂ F c := by
  constructor
  · intro
    change HasMapBifunctor K₁ K₂ F.flip.flip c
    infer_instance
  · intro
    infer_instance

#check mapBifunctor K₁ K₂ F c
#check mapBifunctor K₂ K₁ F.flip c-/

end HomologicalComplex

end CategoryTheory
