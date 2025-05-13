/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.HomotopyCategory.Monoidal
import Mathlib.Algebra.Homology.BifunctorTriangulated

/-!
# The tensor product is triangulated

-/

open CategoryTheory Category Limits MonoidalCategory HomologicalComplex

namespace HomotopyCategory

variable (C : Type*) [Category C] [Preadditive C] [MonoidalCategory C] [HasZeroObject C]
  [HasBinaryBiproducts C] [MonoidalPreadditive C]
  [∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]

variable (K : HomotopyCategory C (.up ℤ))

noncomputable instance : ((curriedTensor _).obj K).CommShift ℤ :=
  inferInstanceAs ((((curriedTensor C).bifunctorMapHomotopyCategory
    (.up ℤ) (.up ℤ) (.up ℤ)).obj K).CommShift ℤ)

noncomputable instance : ((curriedTensor _).flip.obj K).CommShift ℤ :=
  inferInstanceAs ((((curriedTensor C).bifunctorMapHomotopyCategory
    (.up ℤ) (.up ℤ) (.up ℤ)).flip.obj K).CommShift ℤ)

noncomputable instance : ((curriedTensor _).obj K).IsTriangulated :=
  inferInstanceAs ((((curriedTensor C).bifunctorMapHomotopyCategory
    (.up ℤ) (.up ℤ) (.up ℤ)).obj K).IsTriangulated)

noncomputable instance : ((curriedTensor _).flip.obj K).IsTriangulated :=
  inferInstanceAs ((((curriedTensor C).bifunctorMapHomotopyCategory
    (.up ℤ) (.up ℤ) (.up ℤ)).flip.obj K).IsTriangulated)

end HomotopyCategory
