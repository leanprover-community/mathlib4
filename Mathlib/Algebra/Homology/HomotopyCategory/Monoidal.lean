/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.BifunctorHomotopy
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.CategoryTheory.Monoidal.Pentagon
import Mathlib.CategoryTheory.QuotientThree

/-!
# The homotopy category is monoidal

-/

open CategoryTheory Category Limits MonoidalCategory HomologicalComplex

namespace HomotopyCategory

variable (C : Type*) [Category C] [Preadditive C] [MonoidalCategory C] [HasZeroObject C]
  [(curriedTensor C).Additive]
  [∀ (X₁ : C), ((curriedTensor C).obj X₁).Additive]
  {I : Type*} [AddMonoid I] (c : ComplexShape I) [c.TensorSigns]
  [∀ (X₁ X₂ : GradedObject I C), X₁.HasTensor X₂]
  [∀ (X₁ : C), PreservesColimit (Functor.empty C) ((curriedTensor C).obj X₁)]
  [∀ (X₂ : C), PreservesColimit (Functor.empty C) ((curriedTensor C).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject I C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject I C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject I C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃] [DecidableEq I]

noncomputable example : MonoidalCategory (HomologicalComplex C c) := inferInstance

namespace MonoidalCategory

variable [∀ (K₁ K₂ : HomologicalComplex C c), HasMapBifunctor K₁ K₂ (curriedTensor C) c]

noncomputable def unit : HomotopyCategory C c :=
  (quotient _ _).obj (𝟙_ _)

noncomputable def bifunctor :
    HomotopyCategory C c ⥤ HomotopyCategory C c ⥤ HomotopyCategory C c :=
  (curriedTensor C).bifunctorMapHomotopyCategory c c c

noncomputable def bifunctorIso :
    (((whiskeringLeft₂ _).obj (quotient C c)).obj (quotient C c)).obj (bifunctor C c ) ≅
      MonoidalCategory.curriedTensor (HomologicalComplex C c) ⋙
        (whiskeringRight _ _ _).obj (quotient C c) := Iso.refl _

noncomputable def bifunctorComp₁₂Iso :
  ((((whiskeringLeft₃ (HomotopyCategory C c)).obj (quotient C c)).obj
    (quotient C c)).obj (quotient C c)).obj
      (bifunctorComp₁₂ (bifunctor C c) (bifunctor C c)) ≅
    (Functor.postcompose₃.obj (quotient C c)).obj
      (bifunctorComp₁₂ (curriedTensor (HomologicalComplex C c))
        (curriedTensor (HomologicalComplex C c))) :=
  Quotient.bifunctorComp₁₂Iso (bifunctorIso C c) (bifunctorIso C c)

/-
def bifunctorComp₂₃Iso :
  ((((whiskeringLeft₃ (HomotopyCategory C c)).obj (quotient C c)).obj
    (quotient C c)).obj (quotient C c)).obj
      (bifunctorComp₂₃ (bifunctor C c) (bifunctor C c)) ≅
    (Functor.postcompose₃.obj (quotient C c)).obj
      (bifunctorComp₂₃ (curriedTensor (HomologicalComplex C c))
        (curriedTensor (HomologicalComplex C c))) := sorry

noncomputable def associator :
    bifunctorComp₁₂ (bifunctor C c) (bifunctor C c) ≅
      bifunctorComp₂₃ (bifunctor C c) (bifunctor C c) :=
  Quotient.natIsoLift₃ _ _ _
    (bifunctorComp₁₂Iso C c ≪≫ (Functor.postcompose₃.obj (quotient C c)).mapIso
      (curriedAssociatorNatIso (HomologicalComplex C c)) ≪≫
        (bifunctorComp₂₃Iso C c).symm)

noncomputable instance : MonoidalCategory (HomotopyCategory C c) :=
  .ofBifunctor (unit C c) (bifunctor C c) (associator C c) sorry sorry sorry sorry
  -/

end MonoidalCategory

end HomotopyCategory
