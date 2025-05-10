/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.BicomplexColumns
import Mathlib.Algebra.Homology.BifunctorSingle
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.BifunctorColimits
import Mathlib.Algebra.Homology.HomotopyCategory.Monoidal
import Mathlib.Algebra.Homology.HomotopyCategory.Devissage
import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
import Mathlib.Algebra.Homology.Localization
import Mathlib.Algebra.Homology.PreservesQuasiIso
import Mathlib.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import Mathlib.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.ObjectProperty.Shift
import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant

/-!
# Flat objects and K-flat complexes

-/

open CategoryTheory MonoidalCategory Limits Opposite ZeroObject

section

@[simps obj]
def Antitone.functor {α β : Type*} [Preorder α] [Preorder β]
    {f : α → β} (hf : Antitone f) :
    αᵒᵖ ⥤ β where
  obj := fun a ↦ f a.unop
  map φ := homOfLE (hf (leOfHom φ.unop))

lemma Int.antitone_neg : Antitone (fun (n : ℤ) ↦ -n) := fun _ _ _ ↦ by dsimp; omega

@[simps]
def Int.opEquivalence : ℤᵒᵖ ≌ ℤ where
  functor := Int.antitone_neg.functor
  inverse := Int.antitone_neg.functor.rightOp
  unitIso := NatIso.ofComponents (fun n ↦ eqToIso (by simp))
  counitIso := NatIso.ofComponents (fun n ↦ eqToIso (by simp))

end

universe v u

variable (C : Type u) [Category.{v} C] [Abelian C]
  [MonoidalCategory C] [MonoidalPreadditive C]
  [∀ (j : ℤ), HasColimitsOfShape
    (Discrete ↑((ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⁻¹' {j})) C]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]

namespace CochainComplex

variable {C}

open HomologicalComplex

lemma kFlat_iff_preservesQuasiIso (K : CochainComplex C ℤ) :
    (quasiIso C (.up ℤ)).kFlat K ↔
      preservesQuasiIso (tensorLeft K) ∧ preservesQuasiIso (tensorRight K) := Iff.rfl

instance : (quasiIso C (.up ℤ)).kFlat.ContainsZero where
  exists_zero := ⟨_, isZero_zero _, by
    rw [kFlat_iff_preservesQuasiIso]
    constructor
    · apply ObjectProperty.prop_of_isZero
      rw [IsZero.iff_id_eq_zero]
      ext K : 2
      dsimp
      rw [← tensor_id, id_zero, MonoidalPreadditive.zero_tensor]
    · apply ObjectProperty.prop_of_isZero
      rw [IsZero.iff_id_eq_zero]
      ext K : 2
      dsimp
      rw [← tensor_id, id_zero, MonoidalPreadditive.tensor_zero]⟩

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

variable (C) in
lemma closedUnderColimitsOfShape_kFlat (J : Type*) [Category J]
    [HasColimitsOfShape J C] [HasExactColimitsOfShape J C]
    [∀ (X : C), PreservesColimitsOfShape J ((curriedTensor C).flip.obj X)]
    [∀ (X : C), PreservesColimitsOfShape J ((curriedTensor C).obj X)] :
    ClosedUnderColimitsOfShape J (quasiIso C (.up ℤ)).kFlat := by
  intro F c hc hF
  rw [kFlat_iff_preservesQuasiIso]
  have hJ := isStableUnderColimitsOfShape_preservesQuasiIso C C (.up ℤ) (.up ℤ) J
  constructor
  · have : PreservesColimitsOfShape J (curriedTensor (CochainComplex C ℤ)) :=
      inferInstanceAs (PreservesColimitsOfShape _
        (Functor.bifunctorMapHomologicalComplex _ _ _ _))
    exact hJ (isColimitOfPreserves (curriedTensor _) hc) (fun j ↦ (hF j).1)
  · have : PreservesColimitsOfShape J (curriedTensor (CochainComplex C ℤ)).flip :=
      inferInstanceAs (PreservesColimitsOfShape _
        (Functor.bifunctorMapHomologicalComplex _ _ _ _).flip)
    exact hJ (isColimitOfPreserves (curriedTensor _).flip hc) (fun j ↦ (hF j).2)

end CochainComplex

namespace HomotopyCategory

variable {C}

lemma kFlat_iff_preservesQuasiIso (K : HomotopyCategory C (.up ℤ)) :
    (quasiIso C (.up ℤ)).kFlat K ↔
      preservesQuasiIso (tensorLeft K) ∧ preservesQuasiIso (tensorRight K) := Iff.rfl

lemma kFlat_quotient_obj_iff (K : CochainComplex C ℤ) :
    (quasiIso C (.up ℤ)).kFlat ((quotient _ _).obj K) ↔
      (HomologicalComplex.quasiIso C (.up ℤ)).kFlat K := by
  rw [kFlat_iff_preservesQuasiIso, CochainComplex.kFlat_iff_preservesQuasiIso]
  apply and_congr <;> exact Functor.preservesQuasiIso_iff_of_factors (Iso.refl _)

instance : (quasiIso C (.up ℤ)).kFlat.ContainsZero where
  exists_zero := ⟨(quotient _ _).obj 0, Functor.map_isZero _ (isZero_zero _), by
    rw [kFlat_quotient_obj_iff]
    exact ObjectProperty.prop_zero _⟩

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

variable {C}

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

instance : (ObjectProperty.flat (A := C)).ContainsZero where
  exists_zero := ⟨0, isZero_zero C, by
    rw [← kFlat_single_obj_iff_flat _ 0]
    apply ObjectProperty.prop_of_isZero
    apply Functor.map_isZero
    apply Limits.isZero_zero⟩

-- TODO: prove it
variable [(HomotopyCategory.quasiIso C (.up ℤ)).kFlat.IsTriangulatedClosed₂]

instance : (HomotopyCategory.quasiIso C (.up ℤ)).kFlat.IsTriangulated where

lemma kFlat_of_bounded_of_flat (K : CochainComplex C ℤ) (a b : ℤ)
    [K.IsStrictlyGE a] [K.IsStrictlyLE b]
    (hK : ∀ n, ObjectProperty.flat (K.X n)) :
    (quasiIso C (.up ℤ)).kFlat K := by
  rw [← HomotopyCategory.kFlat_quotient_obj_iff]
  apply HomotopyCategory.mem_subcategory_of_strictly_bounded _ K a b
  intro n _ _
  replace hK := hK n
  rw [← kFlat_single_obj_iff_flat _ 0,
    ← HomotopyCategory.kFlat_quotient_obj_iff] at hK
  exact ObjectProperty.prop_of_iso _
    ((HomotopyCategory.singleFunctorPostcompQuotientIso C 0).symm.app (K.X n)) hK

section

variable (K : CochainComplex C ℤ)

@[simps]
noncomputable def coconeStupidFiltrationGE :
    Cocone K.stupidFiltrationGE where
  pt := K
  ι := { app n := K.ιStupidTrunc _ }

noncomputable def isColimitCoconeStupidFiltrationGE :
    IsColimit K.coconeStupidFiltrationGE :=
  HomologicalComplex.isColimitOfEval _ _ (fun n ↦ by
    apply isColimitOfIsEventuallyConstant _ (op n)
    rintro ⟨j⟩ ⟨h⟩
    obtain ⟨i, rfl⟩ := Int.le.dest (leOfHom h)
    exact isIso_ιStupidTrunc_f _ _ rfl)

variable [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X)]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).obj X)]

lemma kFlat_of_isStrictlyLE_of_flat (b : ℤ) [K.IsStrictlyLE b]
    [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
    (hK : ∀ n, ObjectProperty.flat (K.X n)) :
    (quasiIso C (.up ℤ)).kFlat K := by
  apply (closedUnderColimitsOfShape_kFlat C ℤ)
    (K.isColimitCoconeStupidFiltrationGE.whiskerEquivalence
      Int.opEquivalence.symm)
  intro i
  apply kFlat_of_bounded_of_flat (K.stupidTrunc (ComplexShape.embeddingUpIntGE (-i))) (-i) b
  intro n
  by_cases hn : -i ≤ n
  · obtain ⟨k, hk⟩ := Int.le.dest hn
    let φ := (ιStupidTrunc K (ComplexShape.embeddingUpIntGE (-i))).f n
    have : IsIso φ := isIso_ιStupidTrunc_f K _ (i := k) (by dsimp; omega)
    exact ObjectProperty.prop_of_iso _ (asIso φ).symm (hK n)
  · apply ObjectProperty.prop_of_isZero
    apply isZero_stupidTrunc_X K (ComplexShape.embeddingUpIntGE (-i)) n
    intro
    dsimp
    omega

end

end CochainComplex
