/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.BifunctorSingle
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.HomotopyCategory.Monoidal
import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
import Mathlib.Algebra.Homology.Localization
import Mathlib.Algebra.Homology.PreservesQuasiIso
import Mathlib.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import Mathlib.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.ObjectProperty.Shift
import Mathlib.CategoryTheory.Limits.FullSubcategory

/-!
# Flat objects and K-flat complexes

-/

open CategoryTheory MonoidalCategory Limits

universe v u

variable (C : Type u) [Category.{v} C] [Abelian C]
  [MonoidalCategory C] [MonoidalPreadditive C]
  [∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]

namespace CochainComplex

variable {C}

open HomologicalComplex

lemma kFlat_iff_preservesQuasiIso (K : CochainComplex C ℤ) :
    (quasiIso C (.up ℤ)).kFlat K ↔
      preservesQuasiIso (tensorLeft K) ∧ preservesQuasiIso (tensorRight K) := Iff.rfl

instance : (quasiIso C (.up ℤ)).kFlat.IsStableUnderShift ℤ where
  isStableUnderShiftBy n := ⟨fun K hK ↦ by
    rw [ObjectProperty.prop_shift_iff, kFlat_iff_preservesQuasiIso]
    constructor
    · exact (preservesQuasiIso.prop_iff_of_iso
        (bifunctorMapHomologicalComplexObjShiftIso (curriedTensor C) K n)).2
          (hK.1.comp (preservesQuasiIso_shiftFunctor C n))
    · exact (preservesQuasiIso.prop_iff_of_iso
        (bifunctorMapHomologicalComplexFlipObjShiftIso (curriedTensor C) K n)).2
          (hK.2.comp (preservesQuasiIso_shiftFunctor C n))⟩

lemma kFlat_shift_iff (K : CochainComplex C ℤ) (n : ℤ) :
    (quasiIso C (.up ℤ)).kFlat (K⟦n⟧) ↔ (quasiIso C (.up ℤ)).kFlat K := by
  apply ObjectProperty.prop_shift_iff_of_isStableUnderShift

/-lemma closedUnderLimitsOfShape_kFlat (J : Type*) [Category J]
    [HasColimitsOfShape J C] [HasExactColimitsOfShape J C]
    [∀ (X : C), PreservesColimitsOfShape J (tensorLeft X)]
    [∀ (X : C), PreservesColimitsOfShape J (tensorRight X)] :
    ClosedUnderLimitsOfShape J (quasiIso C (.up ℤ)).kFlat := by
  sorry-/

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

instance : (quasiIso C (.up ℤ)).kFlat.IsStableUnderShift ℤ where
  isStableUnderShiftBy n := ⟨fun K hK ↦ by
    obtain ⟨K, rfl⟩ := K.quotient_obj_surjective
    rw [kFlat_quotient_obj_iff] at hK
    rw [ObjectProperty.prop_shift_iff]
    refine ((quasiIso C (ComplexShape.up ℤ)).kFlat.prop_iff_of_iso
      (((quotient C (.up ℤ)).commShiftIso n).app K)).1 ?_
    dsimp
    rw [kFlat_quotient_obj_iff]
    exact (HomologicalComplex.quasiIso C (.up ℤ)).kFlat.le_shift n _ hK⟩

end HomotopyCategory

namespace CochainComplex

open HomologicalComplex

lemma kFlat_single_obj_iff_flat (X : C) (n : ℤ) :
    (quasiIso C (.up ℤ)).kFlat ((single _ _ n).obj X) ↔ ObjectProperty.flat X := by
  trans (quasiIso C (.up ℤ)).kFlat ((single _ _ 0).obj X)
  · rw [← kFlat_shift_iff ((single _ _ 0).obj X) (-n)]
    exact ((quasiIso C (ComplexShape.up ℤ)).kFlat.prop_iff_of_iso
      (((CochainComplex.singleFunctors C).shiftIso (-n) n 0 (by simp)).app X).symm)
  · simp only [kFlat_iff_preservesQuasiIso, ObjectProperty.flat,
      Functor.exactFunctor_iff_preservesQuasiIso _ (.up ℤ) (i₀ := 0) rfl (by simp)]
    apply and_congr
    · exact preservesQuasiIso.prop_iff_of_iso
        (bifunctorMapHomologicalComplexObjSingleIso (curriedTensor C) X)
    · exact preservesQuasiIso.prop_iff_of_iso
        (bifunctorMapHomologicalComplexFlipObjSingleIso (curriedTensor C) X)

end CochainComplex
