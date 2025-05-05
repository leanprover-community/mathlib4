/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.HomotopyCategory.Monoidal
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Monoidal.KFlat

/-!
# The derived category is monoidal
-/

open CategoryTheory MonoidalCategory Limits

universe w v u

variable (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  [MonoidalCategory C] [(curriedTensor C).Additive]
  [∀ (X₁ : C), ((curriedTensor C).obj X₁).Additive]
  [∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂]
  [∀ (X₁ : C), PreservesColimit (Functor.empty C) ((curriedTensor C).obj X₁)]
  [∀ (X₂ : C), PreservesColimit (Functor.empty C) ((curriedTensor C).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]

namespace HomotopyCategory

abbrev localizerMorphismKFlat :=
  (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)).localizerMorphismKFlat

end HomotopyCategory

namespace DerivedCategory

variable [(HomotopyCategory.localizerMorphismKFlat C).IsLeftDerivabilityStructure]

noncomputable instance : MonoidalCategory (DerivedCategory C) :=
  inferInstanceAs (MonoidalCategory (DerivedMonoidal Qh
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))))

noncomputable instance : (Qh (C := C)).LaxMonoidal :=
  inferInstanceAs (toDerivedMonoidal Qh
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))).LaxMonoidal

instance : (curriedTensor (DerivedCategory C)).IsLeftDerivedFunctor₂
    (Functor.LaxMonoidal.μNatTrans Qh) (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) :=
  inferInstanceAs ((curriedTensor (DerivedMonoidal Qh (HomotopyCategory.quasiIso C
    (ComplexShape.up ℤ)))).IsLeftDerivedFunctor₂
    (Functor.LaxMonoidal.μNatTrans (toDerivedMonoidal Qh
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))))
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)))

noncomputable instance : (Q (C := C)).LaxMonoidal :=
  Functor.LaxMonoidal.ofIso (quotientCompQhIso C)

end DerivedCategory
