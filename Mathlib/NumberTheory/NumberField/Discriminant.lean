/-
Copyright (c) 2023 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.Data.Real.Pi.Bounds
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding
import Mathlib.NumberTheory.NumberField.Norm

/-!
# Number field discriminant
This file defines the discriminant of a number field.

## Main definitions

* `NumberField.discr`: the absolute discriminant of a number field.

## Main result

* `NumberField.discr_gt_one`: **Hermite-Minkowski Theorem**. A nontrivial number field has
nontrivial discriminant.

## Tags
number field, discriminant
-/

-- TODO. Rewrite some of the FLT results on the disciminant using the definitions and results of
-- this file

namespace NumberField

open Classical NumberField Matrix NumberField.InfinitePlace FiniteDimensional

open scoped Real

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
  congr
  ext
  simp only [Function.comp_apply, integralBasis_apply, Basis.localizationLocalization_apply,
    Basis.map_apply]
  rfl

open MeasureTheory MeasureTheory.Measure Zspan NumberField.mixedEmbedding
  NumberField.InfinitePlace ENNReal NNReal Complex

theorem _root_.NumberField.mixedEmbedding.volume_fundamentalDomain_latticeBasis :
    volume (fundamentalDomain (latticeBasis K)) =
      (2 : ℝ≥0∞)⁻¹ ^ NrComplexPlaces K * sqrt ‖discr K‖₊ := by
  let f : Module.Free.ChooseBasisIndex ℤ (𝓞 K) ≃ (K →+* ℂ) :=
    (canonicalEmbedding.latticeBasis K).indexEquiv (Pi.basisFun ℂ _)
  let e : (index K) ≃ Module.Free.ChooseBasisIndex ℤ (𝓞 K) := (indexEquiv K).trans f.symm
  let M := (mixedEmbedding.stdBasis K).toMatrix ((latticeBasis K).reindex e.symm)
  let N := Algebra.embeddingsMatrixReindex ℚ ℂ (integralBasis K ∘ f.symm)
    RingHom.equivRatAlgHom
  suffices M.map Complex.ofReal = (matrixToStdBasis K) *
      (Matrix.reindex (indexEquiv K).symm (indexEquiv K).symm N).transpose by
    calc volume (fundamentalDomain (latticeBasis K))
      _ = ‖((mixedEmbedding.stdBasis K).toMatrix ((latticeBasis K).reindex e.symm)).det‖₊ := by
        rw [← fundamentalDomain_reindex _ e.symm, ← norm_toNNReal, measure_fundamentalDomain
          ((latticeBasis K).reindex e.symm), volume_fundamentalDomain_stdBasis, mul_one]
        rfl
      _ = ‖(matrixToStdBasis K).det * N.det‖₊ := by
        rw [← nnnorm_real, ← ofReal_eq_coe, RingHom.map_det, RingHom.mapMatrix_apply, this,
          det_mul, det_transpose, det_reindex_self]
      _ = (2 : ℝ≥0∞)⁻¹ ^ Fintype.card {w : InfinitePlace K // IsComplex w} * sqrt ‖N.det ^ 2‖₊ := by
        have : ‖Complex.I‖₊ = 1 := by rw [← norm_toNNReal, norm_eq_abs, abs_I, Real.toNNReal_one]
        rw [det_matrixToStdBasis, nnnorm_mul, nnnorm_pow, nnnorm_mul, this, mul_one, nnnorm_inv,
          coe_mul, ENNReal.coe_pow, ← norm_toNNReal, IsROrC.norm_two, Real.toNNReal_ofNat,
          coe_inv two_ne_zero, coe_ofNat, nnnorm_pow, NNReal.sqrt_sq]
      _ = (2 : ℝ≥0∞)⁻¹ ^ Fintype.card { w // IsComplex w } * NNReal.sqrt ‖discr K‖₊ := by
        rw [← Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two, Algebra.discr_reindex,
          ← coe_discr, map_intCast, ← Complex.nnnorm_int]
  ext : 2
  dsimp only
  rw [Matrix.map_apply, Basis.toMatrix_apply, Basis.coe_reindex, Function.comp_apply,
    Equiv.symm_symm, latticeBasis_apply, ← commMap_canonical_eq_mixed, Complex.ofReal_eq_coe,
    stdBasis_repr_eq_matrixToStdBasis_mul K _ (fun _ => rfl)]
  rfl

theorem exists_ne_zero_mem_ringOfIntegers_of_norm_le_mul_sqrt_discr :
    ∃ (a : 𝓞 K), a ≠ 0 ∧
      |Algebra.norm ℚ (a:K)| ≤ (4 / π) ^ NrComplexPlaces K *
        (finrank ℚ K).factorial / (finrank ℚ K) ^ (finrank ℚ K) * Real.sqrt |discr K| := by
  -- The smallest possible value for `exists_ne_zero_mem_ringOfIntegers_of_norm_le`
  let B := (minkowskiBound K * (convexBodySumFactor K)⁻¹).toReal ^ (1 / (finrank ℚ K : ℝ))
  have hB : 0 ≤ B := Real.rpow_nonneg toReal_nonneg _
  have h_le : (minkowskiBound K) ≤ volume (convexBodySum K B) := by
    refine le_of_eq ?_
    rw [convexBodySum_volume, ← ENNReal.ofReal_pow hB, ← Real.rpow_nat_cast, ← Real.rpow_mul
      toReal_nonneg, div_mul_cancel _ (Nat.cast_ne_zero.mpr (ne_of_gt finrank_pos)), Real.rpow_one,
      ofReal_toReal, mul_comm, mul_assoc, ENNReal.inv_mul_cancel (convexBodySumFactor_ne_zero K)
      (convexBodySumFactor_ne_top K), mul_one]
    exact mul_ne_top (ne_of_lt (minkowskiBound_lt_top K))
      (ENNReal.inv_ne_top.mpr (convexBodySumFactor_ne_zero K))
  obtain ⟨x, h_nz, h_bd⟩ := exists_ne_zero_mem_ringOfIntegers_of_norm_le K h_le
  refine ⟨x, h_nz, ?_⟩
  convert h_bd
  rw [div_pow B, ← Real.rpow_nat_cast B, ← Real.rpow_mul (by positivity), div_mul_cancel _
    (Nat.cast_ne_zero.mpr <| ne_of_gt finrank_pos), Real.rpow_one, mul_comm_div, mul_div_assoc']
  congr 1
  rw [eq_comm]
  calc
    _ = (2:ℝ)⁻¹ ^ NrComplexPlaces K * sqrt ‖discr K‖₊ * (2:ℝ) ^ finrank ℚ K *
          ((2:ℝ) ^ NrRealPlaces K * (π / 2) ^ NrComplexPlaces K /
          (Nat.factorial (finrank ℚ K)))⁻¹ := by
      simp_rw [minkowskiBound, convexBodySumFactor, volume_fundamentalDomain_latticeBasis,
        toReal_mul, toReal_inv, toReal_div, toReal_mul, coe_toReal, toReal_pow, toReal_inv,
        toReal_ofNat, mixedEmbedding.finrank, toReal_div, toReal_ofNat, coe_toReal, coe_real_pi,
        toReal_nat]
    _ = (2:ℝ) ^ (finrank ℚ K - NrComplexPlaces K - NrRealPlaces K + NrComplexPlaces K : ℤ) *
          Real.sqrt ‖discr K‖ * Nat.factorial (finrank ℚ K) * π⁻¹ ^ (NrComplexPlaces K) := by
      simp_rw [inv_div, div_eq_mul_inv, mul_inv, ← zpow_neg_one, ← zpow_coe_nat, mul_zpow,
        ← zpow_mul, neg_one_mul, mul_neg_one, neg_neg, Real.coe_sqrt, coe_nnnorm, sub_eq_add_neg,
        zpow_add₀ (two_ne_zero : (2:ℝ) ≠ 0)]
      ring
    _ = (2:ℝ) ^ (2 * NrComplexPlaces K : ℤ) * Real.sqrt ‖discr K‖ * Nat.factorial (finrank ℚ K) *
          π⁻¹ ^ (NrComplexPlaces K) := by
      congr
      rw [← card_add_two_mul_card_eq_rank, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      ring
    _ = (4 / π) ^ NrComplexPlaces K * (finrank ℚ K).factorial * Real.sqrt |discr K| := by
      rw [show ‖discr K‖ = |(discr K : ℝ)| by rfl, zpow_mul, show (2:ℝ) ^ (2:ℤ) = 4 by norm_cast,
        div_pow, inv_eq_one_div, div_pow, one_pow, zpow_coe_nat]
      ring

variable {K}

theorem abs_discr_ge (h : 1 < finrank ℚ K) :
    (4 / 9 : ℝ) * (3 * π / 4) ^ finrank ℚ K ≤ |discr K| := by
  -- We use `exists_ne_zero_mem_ringOfIntegers_of_norm_le_mul_sqrt_discr` to get a nonzero
  -- algebraic integer `x` of small norm and the fact that `1 ≤ |Norm x|` to get a lower bound
  -- on `sqrt |discr K|`.
  obtain ⟨x, h_nz, h_bd⟩ := exists_ne_zero_mem_ringOfIntegers_of_norm_le_mul_sqrt_discr K
  have h_nm : (1:ℝ) ≤ |(Algebra.norm ℚ) (x:K)| := by
    rw [← Algebra.coe_norm_int, ← Int.cast_one, ← Int.cast_abs, Rat.cast_coe_int, Int.cast_le]
    exact Int.one_le_abs (Algebra.norm_ne_zero_iff.mpr h_nz)
  replace h_bd := le_trans h_nm h_bd
  rw [← inv_mul_le_iff (by positivity), inv_div, mul_one, Real.le_sqrt (by positivity)
    (by positivity), ← Int.cast_abs, div_pow, mul_pow, ← pow_mul, ← pow_mul] at h_bd
  refine le_trans ?_ h_bd
  -- The sequence `a n` is a lower bound for `|discr K|`. We prove below by induction an uniform
  -- lower bound for this sequence from which we deduce the result.
  let a : ℕ → ℝ := fun n => (n:ℝ) ^ (n * 2) / ((4 / π) ^ n * (n.factorial:ℝ) ^ 2)
  suffices ∀ n, 2 ≤ n → (4 / 9 : ℝ) * (3 * π / 4) ^ n ≤ a n by
    refine le_trans (this (finrank ℚ K) h) ?_
    simp only -- unfold `a` and beta-reduce
    gcongr
    · exact (one_le_div Real.pi_pos).2 Real.pi_le_four
    · rw [← card_add_two_mul_card_eq_rank, mul_comm]
      exact Nat.le_add_left _ _
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact le_of_eq <| by norm_num [Nat.factorial_two]; field_simp; ring
  | succ m _ h_m =>
      suffices (3:ℝ) ≤ (1 + 1 / m : ℝ) ^ (2 * m) by
        convert_to _ ≤ (a m) * (1 + 1 / m : ℝ) ^ (2 * m) / (4 / π)
        · simp_rw [add_mul, one_mul, pow_succ, Nat.factorial_succ]
          field_simp; ring
        · rw [_root_.le_div_iff (by positivity), pow_succ]
          convert (mul_le_mul h_m this (by positivity) (by positivity)) using 1
          field_simp; ring
      refine le_trans (le_of_eq (by field_simp; norm_num)) (one_add_mul_le_pow ?_ (2 * m))
      exact le_trans (by norm_num : (-2:ℝ) ≤ 0) (by positivity)

/-- **Hermite-Minkowski Theorem**. A nontrivial number field has nontrivial discriminant. -/
theorem discr_gt_one (h : 1 < finrank ℚ K) : 2 < |discr K| := by
  have h₁ : 1 ≤ 3 * π / 4 := by
    rw [_root_.le_div_iff (by positivity), ← _root_.div_le_iff' (by positivity), one_mul]
    linarith [Real.pi_gt_three]
  have h₂ : (9:ℝ) < π ^ 2 := by
    rw [ ← Real.sqrt_lt (by positivity) (by positivity), show Real.sqrt (9:ℝ) = 3 from
    (Real.sqrt_eq_iff_sq_eq (by positivity) (by positivity)).mpr (by norm_num)]
    exact Real.pi_gt_three
  refine Int.cast_lt.mp <| lt_of_lt_of_le ?_ (abs_discr_ge h)
  rw [← _root_.div_lt_iff' (by positivity), Int.int_cast_ofNat]
  refine lt_of_lt_of_le ?_ (pow_le_pow_right (n := 2) h₁ h)
  rw [div_pow, _root_.lt_div_iff (by norm_num), mul_pow]
  norm_num
  rw [ ← _root_.div_lt_iff' (by positivity), show (72:ℝ) / 9 = 8 by norm_num]
  linarith [h₂]

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
      rw [Basis.map_apply, RingEquiv.toAddEquiv_eq_coe, AddEquiv.toIntLinearEquiv_symm,
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
  replace h' : ∀ i j, IsIntegral ℤ (b'.toMatrix (b.reindex (b.indexEquiv b')) i j)
  · intro i j
    convert h' i ((b.indexEquiv b').symm j)
-- Porting note: `simp; rfl` was `simpa`.
    simp; rfl
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
    refine' isUnit_iff_exists_inv.2 ⟨r', _⟩
    suffices algebraMap ℤ ℚ (r * r') = 1 by
      rw [← RingHom.map_one (algebraMap ℤ ℚ)] at this
      exact (IsFractionRing.injective ℤ ℚ) this
    rw [RingHom.map_mul, hr, hr', ← Matrix.det_mul,
      Basis.toMatrix_mul_toMatrix_flip, Matrix.det_one]
  rw [← RingHom.map_one (algebraMap ℤ ℚ), ← hr]
  cases' Int.isUnit_iff.1 hunit with hp hm
  · simp [hp]
  · simp [hm]
#align algebra.discr_eq_discr_of_to_matrix_coeff_is_integral Algebra.discr_eq_discr_of_toMatrix_coeff_isIntegral
