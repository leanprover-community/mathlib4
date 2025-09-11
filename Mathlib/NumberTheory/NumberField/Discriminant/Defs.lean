/-
Copyright (c) 2023 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Init.Data.ULift
import Init.Data.Fin.Fold
import Init.Data.List.Nat.Pairwise
import Init.Data.List.Nat.Range
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Localization.NormTrace
import Mathlib.Analysis.Normed.Field.Lemmas

/-!
# Number field discriminant
This file defines the discriminant of a number field.

## Main definitions

* `NumberField.discr`: the absolute discriminant of a number field.

## Tags
number field, discriminant
-/

open Module

-- TODO: Rewrite some of the FLT results on the discriminant using the definitions and results of
-- this file

namespace NumberField

variable (K : Type*) [Field K] [NumberField K]

/-- The absolute discriminant of a number field. -/
noncomputable abbrev discr : ℤ := Algebra.discr ℤ (RingOfIntegers.basis K)

theorem coe_discr : (discr K : ℚ) = Algebra.discr ℚ (integralBasis K) :=
  (Algebra.discr_localizationLocalization ℤ _ K (RingOfIntegers.basis K)).symm

theorem discr_ne_zero : discr K ≠ 0 := by
  rw [← (Int.cast_injective (α := ℚ)).ne_iff, coe_discr]
  exact Algebra.discr_not_zero_of_basis ℚ (integralBasis K)

theorem discr_eq_discr {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℤ (𝓞 K)) :
    Algebra.discr ℤ b = discr K := by
  let b₀ := Basis.reindex (RingOfIntegers.basis K) (Basis.indexEquiv (RingOfIntegers.basis K) b)
  rw [Algebra.discr_eq_discr (𝓞 K) b b₀, Basis.coe_reindex, Algebra.discr_reindex]

theorem discr_eq_discr_of_algEquiv {L : Type*} [Field L] [NumberField L] (f : K ≃ₐ[ℚ] L) :
    discr K = discr L := by
  let f₀ : 𝓞 K ≃ₗ[ℤ] 𝓞 L := (f.restrictScalars ℤ).mapIntegralClosure.toLinearEquiv
  rw [← Rat.intCast_inj, coe_discr, Algebra.discr_eq_discr_of_algEquiv (integralBasis K) f,
    ← discr_eq_discr L ((RingOfIntegers.basis K).map f₀)]
  change _ = algebraMap ℤ ℚ _
  rw [← Algebra.discr_localizationLocalization ℤ (nonZeroDivisors ℤ) L]
  congr 1
  ext
  simp only [Function.comp_apply, integralBasis_apply, Basis.localizationLocalization_apply,
    Basis.map_apply]
  rfl

theorem discr_eq_discr_of_ringEquiv {L : Type*} [Field L] [NumberField L] (f : K ≃+* L) :
    discr K = discr L :=
  discr_eq_discr_of_algEquiv _ <| AlgEquiv.ofRingEquiv (f := f) fun _ ↦ by simp

end NumberField

namespace Rat

open NumberField

/-- The absolute discriminant of the number field `ℚ` is 1. -/
@[simp]
theorem numberField_discr : discr ℚ = 1 := by
  let b : Basis (Fin 1) ℤ (𝓞 ℚ) :=
    Basis.map (Basis.singleton (Fin 1) ℤ) ringOfIntegersEquiv.toAddEquiv.toIntLinearEquiv.symm
  calc NumberField.discr ℚ
    _ = Algebra.discr ℤ b := by convert (discr_eq_discr ℚ b).symm
    _ = Algebra.trace ℤ (𝓞 ℚ) (b default * b default) := by
      rw [Algebra.discr_def, Matrix.det_unique, Algebra.traceMatrix_apply, Algebra.traceForm_apply]
    _ = Algebra.trace ℤ (𝓞 ℚ) 1 := by
      rw [Basis.map_apply, RingEquiv.toAddEquiv_eq_coe, ← AddEquiv.toIntLinearEquiv_symm,
        AddEquiv.coe_toIntLinearEquiv, Basis.singleton_apply,
        show (AddEquiv.symm ↑ringOfIntegersEquiv) (1 : ℤ) = ringOfIntegersEquiv.symm 1 by rfl,
        map_one, mul_one]
    _ = 1 := by rw [Algebra.trace_eq_matrix_trace b]; norm_num

alias _root_.NumberField.discr_rat := numberField_discr

end Rat

variable {ι ι'} (K) [Field K] [DecidableEq ι] [DecidableEq ι'] [Fintype ι] [Fintype ι']

/-- If `b` and `b'` are `ℚ`-bases of a number field `K` such that
`∀ i j, IsIntegral ℤ (b.toMatrix b' i j)` and `∀ i j, IsIntegral ℤ (b'.toMatrix b i j)` then
`discr ℚ b = discr ℚ b'`. -/
theorem Algebra.discr_eq_discr_of_toMatrix_coeff_isIntegral [NumberField K]
    {b : Basis ι ℚ K} {b' : Basis ι' ℚ K} (h : ∀ i j, IsIntegral ℤ (b.toMatrix b' i j))
    (h' : ∀ i j, IsIntegral ℤ (b'.toMatrix b i j)) : discr ℚ b = discr ℚ b' := by
  replace h' : ∀ i j, IsIntegral ℤ (b'.toMatrix (b.reindex (b.indexEquiv b')) i j) := by
    intro i j
    convert h' i ((b.indexEquiv b').symm j)
    simp [Basis.toMatrix_apply]
  classical
  rw [← (b.reindex (b.indexEquiv b')).toMatrix_map_vecMul b', discr_of_matrix_vecMul,
    ← one_mul (discr ℚ b), Basis.coe_reindex, discr_reindex]
  congr
  have hint : IsIntegral ℤ ((b.reindex (b.indexEquiv b')).toMatrix b').det :=
    IsIntegral.det fun i j => h _ _
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  have hunit : IsUnit r := by
    have : IsIntegral ℤ (b'.toMatrix (b.reindex (b.indexEquiv b'))).det :=
      IsIntegral.det fun i j => h' _ _
    obtain ⟨r', hr'⟩ := IsIntegrallyClosed.isIntegral_iff.1 this
    refine isUnit_iff_exists_inv.2 ⟨r', ?_⟩
    suffices algebraMap ℤ ℚ (r * r') = 1 by
      rw [← RingHom.map_one (algebraMap ℤ ℚ)] at this
      exact (IsFractionRing.injective ℤ ℚ) this
    rw [RingHom.map_mul, hr, hr', ← Matrix.det_mul,
      Basis.toMatrix_mul_toMatrix_flip, Matrix.det_one]
  rw [← RingHom.map_one (algebraMap ℤ ℚ), ← hr]
  rcases Int.isUnit_iff.1 hunit with hp | hm
  · simp [hp]
  · simp [hm]
