/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.BifunctorSingle
import Mathlib.Algebra.Homology.HomotopyCategory.Monoidal
import Mathlib.Algebra.Homology.Localization
import Mathlib.Algebra.Homology.PreservesQuasiIso
import Mathlib.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.KFlat

/-!
# Flat objects and K-flat complexes

-/

open CategoryTheory MonoidalCategory Limits

universe v u

variable (C : Type u) [Category.{v} C] [Abelian C]
  [MonoidalCategory C] [MonoidalPreadditive C]
  [∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂]
  [∀ (X₁ : C), PreservesColimit (Functor.empty C) ((curriedTensor C).obj X₁)]
  [∀ (X₂ : C), PreservesColimit (Functor.empty C) ((curriedTensor C).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]

namespace CochainComplex

open HomologicalComplex

lemma kFlat_iff_preservesQuasiIso (K : CochainComplex C ℤ) :
    (quasiIso C (.up ℤ)).kFlat K ↔
      preservesQuasiIso (tensorLeft K) ∧ preservesQuasiIso (tensorRight K) := Iff.rfl

end CochainComplex

namespace HomotopyCategory

lemma kFlat_iff_preservesQuasiIso (K : HomotopyCategory C (.up ℤ)) :
    (quasiIso C (.up ℤ)).kFlat K ↔
      preservesQuasiIso (tensorLeft K) ∧ preservesQuasiIso (tensorRight K) := Iff.rfl

lemma kFlat_quotient_obj_iff (K : CochainComplex C ℤ) :
    (quasiIso C (.up ℤ)).kFlat ((quotient _ _).obj K) ↔
      (HomologicalComplex.quasiIso C (.up ℤ)).kFlat K := by
  rw [kFlat_iff_preservesQuasiIso, CochainComplex.kFlat_iff_preservesQuasiIso]
  apply and_congr <;> exact Functor.preservesQuasiIso_iff_of_factors (Iso.refl _)

end HomotopyCategory

namespace CochainComplex

open HomologicalComplex

lemma kFlat_single_obj_iff_flat (X : C) :
    (quasiIso C (.up ℤ)).kFlat ((single _ _ 0).obj X) ↔
      ObjectProperty.flat X := by
  simp only [kFlat_iff_preservesQuasiIso, ObjectProperty.flat,
    Functor.exactFunctor_iff_preservesQuasiIso _ (.up ℤ) (i₀ := 0) rfl (by simp)]
  apply and_congr
  · exact preservesQuasiIso.prop_iff_of_iso
      (bifunctorMapHomologicalComplexObjSingleIso (curriedTensor C) X)
  · exact preservesQuasiIso.prop_iff_of_iso
      (bifunctorMapHomologicalComplexFlipObjSingleIso (curriedTensor C) X)

end CochainComplex
