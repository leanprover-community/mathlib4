/-
Copyright (c) 2026 Kevin H. Wilson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin H. Wilson
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.CircleAverage

/-!
# Fourier Coefficients of Polynomials

We compute the Fourier coefficient of a polyhnomial over the circle. We also provide a
specialization of Parseval's identity, which in the case of polynomials states that the sum
of the squares of the norms of the coefficients of the polynomial is equal to the average over the
circle of the norm square of the polynomial.

## Main results

- `Polynomial.fourierCoeffOn_cicleMap`: An explicit calculation that teh `n`th Fourier coefficient
  of a polynomial equals its `n`th coefficient.
- `Polynomial.sum_sq_norm_coeff_eq_circleAverage`: Parseval's identity that the sum
  of the squares of the norms of the coefficients of the polynomial is equal to the average over the
  circle of the norm square of the polynomial.

-/

open Complex MeasureTheory Set

namespace Polynomial

@[expose] public section complex

variable (p : ℂ[X])

lemma fourierCoeffOn_cexp (n k : ℤ) :
    fourierCoeffOn Real.two_pi_pos (fun t ↦ Complex.exp (k * (t * Complex.I))) n =
    if n = k then 1 else 0 := by
  rw [fourierCoeffOn_eq_integral]
  simp only [fourier_coe_apply]
  have : ∀ x : ℝ, 2 * Real.pi * I * ↑(-n) * ↑x / ↑(2 * Real.pi - 0) + k * (x * I)
      = ((k - n) * Complex.I) * x := by
    intros x; norm_num; field_simp; ring
  simp_rw [smul_eq_mul, ← Complex.exp_add, this]
  split_ifs with h
  · subst h
    simp only [sub_zero, one_div, mul_inv_rev, sub_self, zero_mul, exp_zero,
      intervalIntegral.integral_const, real_smul, ofReal_mul, ofReal_ofNat, mul_one, ofReal_inv]
    field_simp
  · -- Case k ≠ n: orthogonality gives 0
    rw [integral_exp_mul_complex]
    · simp only [sub_zero, one_div, mul_inv_rev, ofReal_mul, ofReal_ofNat, ofReal_zero, mul_zero,
        exp_zero, real_smul, ofReal_inv, mul_eq_zero, inv_eq_zero, ofReal_eq_zero, Real.pi_ne_zero,
        OfNat.ofNat_ne_zero, or_self, div_eq_zero_iff, I_ne_zero, or_false, false_or]
      norm_cast
      conv => arg 1; arg 1; arg 1; arg 1; rw [mul_assoc]; arg 2; rw [mul_comm]
      rw [Complex.exp_int_mul_two_pi_mul_I]
      simp only [sub_self, true_or]
    simp only [ne_eq, mul_eq_zero, I_ne_zero, or_false];
    norm_cast; rw [sub_eq_zero, ← ne_eq]; symm; exact h

/-- The Fourier coefficient of a polynomial on the unit circle matches the polynomial coefficient -/
lemma fourierCoeffOn_circleMap (p : ℂ[X]) (n : ℤ) :
    fourierCoeffOn Real.two_pi_pos (fun t => p.eval (circleMap 0 1 t)) n =
    if 0 ≤ n then p.coeff n.natAbs else 0 := by
  simp_rw [fourierCoeffOn_eq_integral, p.eval_eq_sum, circleMap, zero_add, ofReal_one, one_mul]
  conv_lhs => {
    enter [2, 1]; ext x; rw [p.sum_def, Finset.smul_sum];
    arg 2; ext e; enter [2, 2]; rw [← Complex.exp_nat_mul] }
  rw [intervalIntegral.integral_finset_sum, Finset.smul_sum]
  · conv_lhs => arg 2; ext x; rw [← fourierCoeffOn_eq_integral _ _ Real.two_pi_pos]
    simp_rw [fourierCoeffOn.const_mul]
    conv_lhs => {
      arg 2; ext k; arg 2;
      rw [show (k : ℂ) = ((k : ℤ) : ℂ) by norm_num, fourierCoeffOn_cexp n k] }
    -- Now we have a sum of scaled Fourier coefficients
    -- Use orthogonality: fourierCoeffOn of exp(k*θ*I) is nonzero only when k relates to n
    split_ifs with hn
    · rw [Finset.sum_eq_single n.natAbs]
      · simp [Int.ofNat_natAbs_of_nonneg hn]
      · intros b hb hbn
        simp only [mul_ite, mul_one, mul_zero, ite_eq_right_iff]
        intros hbn'
        exfalso
        rw [hbn'] at hbn
        norm_num at hbn
      · intros hn'
        have := mem_support_iff.not.mp hn'
        push_neg at this
        simp [Int.ofNat_natAbs_of_nonneg hn, this]
    · -- Case: n < 0
      -- All Fourier coefficients vanish for negative n
      push_neg at hn
      apply Finset.sum_eq_zero
      intro i hi
      simp only [mul_ite, mul_one, mul_zero, ite_eq_right_iff]
      intros hn'
      exfalso
      linarith [hn']
  · intros i hi
    apply Continuous.intervalIntegrable
    continuity

private lemma fourierCoeff_zero (p : ℂ[X]) (n : ℤ) :
    n ∉ p.support.map ⟨Int.ofNat, Int.ofNat_injective⟩ →
    (fourierCoeffOn Real.two_pi_pos (fun t => p.eval (circleMap 0 1 t)) n) = 0 := by
  intros hn
  by_cases hn' : n < 0
  · simp [hn', fourierCoeffOn_circleMap]
  · push_neg at hn'
    simp [hn', fourierCoeffOn_circleMap]
    have hn'' : n.natAbs ∉ p.support := by
      rw [Finset.mem_map] at hn
      push_neg at hn
      by_contra!
      specialize hn n.natAbs this
      simp at hn
      linarith
    simpa using mem_support_iff.not.mp hn''

/-- **Parseval's Identity** for polynomials -/
theorem sum_sq_norm_coeff_eq_circleAverage : ∑ i ∈ p.support, ‖p.coeff i‖ ^ 2 =
    Real.circleAverage ((· ^ 2) ∘ norm ∘ p.eval) 0 1 := by
  -- The Fourier coefficients match the polynomial coefficients
  have coeff_match : ∑ i ∈ p.support, ‖p.coeff i‖ ^ 2 =
    ∑' (n : ℤ), ‖fourierCoeffOn Real.two_pi_pos (fun t => p.eval (circleMap 0 1 t)) n‖ ^ 2 := by
    -- Use fourierCoeff_polynomial_zero to reduce infinite sum to finite sum over support
    symm
    have h_vanish : ∀ n : ℤ, n ∉ p.support.map ⟨Int.ofNat, Int.ofNat_injective⟩ →
        ‖fourierCoeffOn Real.two_pi_pos
          (fun t => p.eval (circleMap 0 1 t)) n‖ ^ 2 = 0 := by
      intro n hn
      rw [fourierCoeff_zero p n hn]
      simp
    rw [tsum_eq_sum h_vanish]
    -- Now we have a sum over support.map, convert to sum over support
    rw [Finset.sum_map]
    congr 1
    ext (i : ℕ)
    simp only [Function.Embedding.coeFn_mk]
    rw [fourierCoeffOn_circleMap]
    split_ifs with h
    · simp [Int.natAbs_natCast]
    · simp only [norm_zero, sq]
      have hi : ¬(0 ≤ Int.ofNat i ∧ Int.ofNat i ≤ p.natDegree) := by rw [not_and_or]; left; exact h
      simp only [Int.natCast_nonneg, true_and, not_le, Int.ofNat_eq_natCast] at hi
      rw [coeff_eq_zero_of_natDegree_lt (by omega : p.natDegree < i)]
      simp

  -- Apply Parseval's identity: ∑ ‖f̂(n)‖² = ∫ ‖f(t)‖² dt
  have parseval : ∑' (n : ℤ), ‖fourierCoeffOn Real.two_pi_pos
      (fun t => p.eval (circleMap 0 1 t)) n‖ ^ 2 =
    (2 * Real.pi)⁻¹ * ∫ t in (0)..(2 * Real.pi), ‖p.eval (circleMap 0 1 t)‖ ^ 2 := by
    have h_cont : Continuous (fun t => p.eval (circleMap 0 1 t)) := by
      exact Continuous.comp (Polynomial.continuous p) (continuous_circleMap 0 1)
    -- Continuous functions on bounded intervals are in L^p
    have h_memLp : MemLp (fun t => p.eval (circleMap 0 1 t)) 2
      (volume.restrict (Ioc 0 (2 * Real.pi))) := by
      constructor
      · exact h_cont.aestronglyMeasurable
      · simp only [eLpNorm, OfNat.ofNat_ne_zero, ↓reduceIte, ENNReal.ofNat_ne_top, eLpNorm',
          ENNReal.toReal_ofNat, ENNReal.rpow_ofNat, one_div]
        apply (ENNReal.rpow_lt_top_iff_of_pos (by norm_num)).mpr
        apply setLIntegral_lt_top_of_bddAbove
        · simp only [Real.volume_Ioc]
          exact ENNReal.ofReal_ne_top
        · apply BddAbove.mono (Set.image_mono Set.Ioc_subset_Icc_self)
          exact (isCompact_Icc.image (by continuity)).bddAbove

    -- Apply Parseval's identity and simplify
    have h_parseval := hasSum_sq_fourierCoeffOn Real.two_pi_pos h_memLp
    rw [h_parseval.tsum_eq]
    norm_num

  exact coeff_match.trans parseval

end complex

end Polynomial
