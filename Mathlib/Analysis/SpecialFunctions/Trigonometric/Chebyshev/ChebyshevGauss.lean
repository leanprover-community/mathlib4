/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuval Filmus
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality
public import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Algebra.Polynomial.Sequence

/-!
# Chebyshev polynomials over the reals: Chebyshev–Gauss

The Chebyshev–Gauss property calculates an integral of a polynomial of degree `< 2 * n`
with respect to the weight function `√(1 - x ^ 2)⁻¹` supported on `[-1, 1]` by a sum
over appropriate evaluations of the polynomial.

## Main statements

* integral_eq_sumZeroes: The integral of a polynomial of degree `< 2 * n` with respect to the weight
  function `√(1 - x ^ 2)⁻¹` supported on `[-1, 1]` is equal to `π` times the average of its values
  on the points `cos ((2 * i + 1) / (2 * n) * π)` for `0 ≤ i < n`.

## Implementation

The statement is proved for Chebyshev polynomials using the complex exponential representation
of `cos`, and then deduced for arbitrary polynomials.
-/

public section

namespace Polynomial.Chebyshev

open Real Polynomial Finset
open Complex (exp I)

private lemma exp_sub_one_ne_zero {n : ℕ} {k : ℤ} (hn : n ≠ 0) (hk : ¬ (2 * n : ℤ) ∣ k) :
    exp (k / n * π * I) ≠ 1 := by
  contrapose hk
  obtain ⟨m, hx⟩ := Complex.exp_eq_one_iff.mp hk
  have h : k = 2 * n * m := by
    apply (@Int.cast_inj ℂ _ _).mp
    linear_combination (norm := (push_cast; field [show (n : ℂ) ≠ 0 by aesop])) hx * (n / π / I)
  use m

private theorem sum_exp {n : ℕ} {k : ℤ} (hn : n ≠ 0) (hk : ¬ (2 * n : ℤ) ∣ k) :
    ∑ i ∈ range n, exp ((k * ((2 * i + 1) / (2 * n) * π)) * I) =
      (exp (k / (2 * n) * π * I) / (exp (k / n * π * I) - 1)) * ((-1) ^ k - 1) := by
  suffices (∑ i ∈ range n, exp ((k * ((2 * i + 1) / (2 * n) * π)) * I)) *
    exp (-(k / (2 * n) * π * I)) * (exp (k / n * π * I) - 1) = (-1) ^ k - 1 by
    rw [Complex.exp_neg] at this
    have hf {s a b t : ℂ} (h : s * a⁻¹ * b = t) (ha : a ≠ 0) (hb : b ≠ 0) : s = a / b * t := by
      linear_combination (norm := field) h * a / b
    apply hf this (Complex.exp_ne_zero _) (by grind [exp_sub_one_ne_zero])
  convert geom_sum_mul (exp (k / n * π * I)) n using 1
  · simp_rw [sum_mul]
    congr! 1 with i hi
    rw [← Complex.exp_nat_mul, ← Complex.exp_add]
    grind
  · rw [← Complex.exp_nat_mul,
      show (n * (k / n * π * I)) = k * (π * I) by field [show (n : ℂ) ≠ 0 by aesop],
      Complex.exp_int_mul, Complex.exp_pi_mul_I]

/-- Weighted sum of `P (x)` where `x` goes over `cos ((2 * i + 1) / (2 * n) * π)` for
  `0 ≤ i < n`. -/
noncomputable def sumZeroes (n : ℕ) (P : ℝ[X]) : ℝ :=
    (π / n) * ∑ i ∈ range n, P.eval (cos ((2 * i + 1) / (2 * n) * π))

@[simp]
theorem sumZeroes_sum (n : ℕ) {ι : Type*} (s : Finset ι) (P : ι → ℝ[X]) :
    sumZeroes n (∑ i ∈ s, P i) = ∑ i ∈ s, sumZeroes n (P i) := by
  simp_rw [sumZeroes, eval_finsetSum]
  rw [sum_comm, mul_sum]

@[simp]
theorem sumZeroes_smul (n : ℕ) (c : ℝ) (P : ℝ[X]) :
    sumZeroes n (c • P) = c * sumZeroes n P := by
  simp_rw [sumZeroes, eval_smul, ← smul_sum, smul_eq_mul]; ring

theorem sumZeroes_T_zero {n : ℕ} (hn : n ≠ 0) : sumZeroes n (T ℝ 0) = π := by
  simp [sumZeroes, show π / n * n = π by field]

theorem sumZeroes_T_of_not_dvd {n : ℕ} {k : ℤ} (hk : ¬ (2 * n : ℤ) ∣ k) :
    sumZeroes n (T ℝ k) = 0 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [sumZeroes]
  suffices ∑ i ∈ range n, 2 * cos (k * ((2 * i + 1) / (2 * n) * π)) = 0 by
    rw [sumZeroes, mul_eq_zero_iff_left (by aesop)]
    rw [← mul_sum, mul_eq_zero_iff_left (by norm_num)] at this
    simpa [T_real_cos]
  suffices (∑ i ∈ range n, 2 * cos (k * ((2 * i + 1) / (2 * n) * π)) : ℂ) = 0 by norm_cast at this ⊢
  suffices ∑ i ∈ range n, 2 * Complex.cos (k * ((2 * i + 1) / (2 * n) * π)) = 0 by aesop
  simp_rw [Complex.two_cos, ← neg_mul, ← Int.cast_neg]
  have : (-1 : ℂ) ^ (-k) = (-1) ^ k := by rw [← Int.cast_negOnePow, ← Int.cast_negOnePow]; simp
  rw [sum_add_distrib, sum_exp hn hk, sum_exp hn (by aesop),
    Int.cast_neg, neg_div, neg_mul, neg_mul, Complex.exp_neg,
    neg_div, neg_mul, neg_mul, Complex.exp_neg, this, ← add_mul, mul_eq_zero_of_left]
  set z := exp (k / (2 * n) * π * I) with hz
  have hz₂ : exp (k / n * π * I) = z ^ 2 := by rw [hz, ← Complex.exp_nat_mul]; grind
  rw [hz₂, ← inv_pow z 2]
  field [show z ≠ 0 by grind [Complex.exp_ne_zero],
    show (z ^ 2 - 1 ≠ 0) ∧ (1 - z ^ 2 ≠ 0) by grind [exp_sub_one_ne_zero]]

/-- The integral of a polynomial of degree `< 2 * n` with respect to the weight function
  `√(1 - x ^ 2)⁻¹` supported on `[-1, 1]` is equal to `π` times the average of its values
  on the points `cos ((2 * i + 1) / (2 * n) * π)` for `0 ≤ i < n`. -/
theorem integral_eq_sumZeroes {n : ℕ} {P : ℝ[X]} (hn : n ≠ 0) (hP : P.degree < 2 * n) :
    ∫ x, P.eval x ∂measureT = sumZeroes n P := by
  have hmem : P ∈ degreeLT ℝ (2 * n) := by rwa [mem_degreeLT]
  rw [← Sequence.span_degreeLT (chebyshevTsequence ℝ) (by simp),
    show Set.Iio (2 * n) = Finset.range (2 * n) by simp,
    Submodule.mem_span_image_finset_iff_exists_fun'] at hmem
  obtain ⟨c, rfl⟩ := hmem
  simp_rw [eval_finsetSum, eval_smul]
  rw [MeasureTheory.integral_finsetSum, sumZeroes_sum]
  · simp_rw [sumZeroes_smul, smul_eq_mul, MeasureTheory.integral_const_mul]
    congr! with i hrange
    simp_rw [chebyshevTsequence]
    by_cases i = 0
    case pos hi => rw [hi, Nat.cast_zero, integral_eval_T_real_measureT_zero, sumZeroes_T_zero hn]
    case neg hi =>
      have : ¬ (2 * n : ℤ) ∣ i := by
        refine (Int.not_dvd_iff_lt_mul_succ _ (by grind)).mpr ⟨0, ⟨by grind, ?_⟩⟩
        rw_mod_cast [zero_add, mul_one]
        exact mem_range.mp hrange
      rw [integral_eval_T_real_measureT_of_ne_zero (by grind), sumZeroes_T_of_not_dvd this]
  · simp_rw [← eval_smul]
    exact fun i hi => integrable_measureT (by fun_prop)

end Polynomial.Chebyshev
