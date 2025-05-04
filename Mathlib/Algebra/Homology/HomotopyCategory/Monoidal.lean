/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.HomotopyCategory
import Mathlib.Algebra.Homology.Monoidal

/-!
# The homotopy category is monoidal

-/

open CategoryTheory Limits MonoidalCategory

namespace HomotopyCategory

variable {C : Type*} [Category C] [Preadditive C] [MonoidalCategory C] [HasZeroObject C]
  [(curriedTensor C).Additive]
  [∀ (X₁ : C), ((curriedTensor C).obj X₁).Additive]
  {I : Type*} [AddMonoid I] (c : ComplexShape I) [c.TensorSigns]
  [∀ (X₁ X₂ : GradedObject I C), X₁.HasTensor X₂]
  [∀ (X₁ : C), PreservesColimit (Functor.empty C) ((curriedTensor C).obj X₁)]
  [∀ (X₂ : C), PreservesColimit (Functor.empty C) ((curriedTensor C).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject I C), X₁.HasTensor₄ObjExt X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject I C), X₁.HasGoodTensor₁₂Tensor X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject I C), X₁.HasGoodTensorTensor₂₃ X₂ X₃] [DecidableEq I]

noncomputable example : MonoidalCategory (HomologicalComplex C c) := inferInstance

namespace MonoidalCategory

--def curriedTensor : HomotopyCategory C c ⥤ HomotopyCategory C c ⥤ HomotopyCategory C c := sorry

end MonoidalCategory

end HomotopyCategory
