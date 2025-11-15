/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Yaël Dillies
-/
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Trigonometric functions as sums of infinite series

In this file we express trigonometric functions in terms of their series expansion.

## Main results

* `Complex.hasSum_cos`, `Complex.cos_eq_tsum`: `Complex.cos` as the sum of an infinite series.
* `Real.hasSum_cos`, `Real.cos_eq_tsum`: `Real.cos` as the sum of an infinite series.
* `Complex.hasSum_sin`, `Complex.sin_eq_tsum`: `Complex.sin` as the sum of an infinite series.
* `Real.hasSum_sin`, `Real.sin_eq_tsum`: `Real.sin` as the sum of an infinite series.
-/

open NormedSpace

open scoped Nat

/-! ### `cos` and `sin` for `ℝ` and `ℂ` -/


section SinCos

theorem Complex.hasSum_cos' (z : ℂ) :
    HasSum (fun n : ℕ => (z * Complex.I) ^ (2 * n) / ↑(2 * n)!) (Complex.cos z) := by
  rw [Complex.cos, Complex.exp_eq_exp_ℂ]
  have := ((expSeries_div_hasSum_exp (z * Complex.I)).add
    (expSeries_div_hasSum_exp (-z * Complex.I))).div_const 2
  replace := (Nat.divModEquiv 2).symm.hasSum_iff.mpr this
  dsimp [Function.comp_def] at this
  simp_rw [← mul_comm 2 _] at this
  refine this.prod_fiberwise fun k => ?_
  dsimp only
  convert hasSum_fintype (_ : Fin 2 → ℂ) using 1
  rw [Fin.sum_univ_two]
  simp_rw [Fin.val_zero, Fin.val_one, add_zero, pow_succ, pow_mul, mul_pow, neg_sq, ← two_mul,
    neg_mul, mul_neg, neg_div, add_neg_cancel, zero_div, add_zero,
    mul_div_cancel_left₀ _ (two_ne_zero : (2 : ℂ) ≠ 0)]

theorem Complex.hasSum_sin' (z : ℂ) :
    HasSum (fun n : ℕ => (z * Complex.I) ^ (2 * n + 1) / ↑(2 * n + 1)! / Complex.I)
      (Complex.sin z) := by
  rw [Complex.sin, Complex.exp_eq_exp_ℂ]
  have := (((expSeries_div_hasSum_exp (-z * Complex.I)).sub
    (expSeries_div_hasSum_exp (z * Complex.I))).mul_right Complex.I).div_const 2
  replace := (Nat.divModEquiv 2).symm.hasSum_iff.mpr this
  dsimp [Function.comp_def] at this
  simp_rw [← mul_comm 2 _] at this
  refine this.prod_fiberwise fun k => ?_
  dsimp only
  convert hasSum_fintype (_ : Fin 2 → ℂ) using 1
  rw [Fin.sum_univ_two]
  simp_rw [Fin.val_zero, Fin.val_one, add_zero, pow_succ, pow_mul, mul_pow, neg_sq, sub_self,
    zero_mul, zero_div, zero_add, neg_mul, mul_neg, neg_div, ← neg_add', ← two_mul,
    neg_mul, neg_div, mul_assoc, mul_div_cancel_left₀ _ (two_ne_zero : (2 : ℂ) ≠ 0), Complex.div_I]

/-- The power series expansion of `Complex.cos`. -/
theorem Complex.hasSum_cos (z : ℂ) :
    HasSum (fun n : ℕ => (-1) ^ n * z ^ (2 * n) / ↑(2 * n)!) (Complex.cos z) := by
  convert Complex.hasSum_cos' z using 1
  simp_rw [mul_pow, pow_mul, Complex.I_sq, mul_comm]

/-- The power series expansion of `Complex.sin`. -/
theorem Complex.hasSum_sin (z : ℂ) :
    HasSum (fun n : ℕ => (-1) ^ n * z ^ (2 * n + 1) / ↑(2 * n + 1)!) (Complex.sin z) := by
  convert Complex.hasSum_sin' z using 1
  simp_rw [mul_pow, pow_succ, pow_mul, Complex.I_sq, ← mul_assoc, mul_div_assoc, div_right_comm,
    div_self Complex.I_ne_zero, mul_comm _ ((-1 : ℂ) ^ _), mul_one_div, mul_div_assoc, mul_assoc]

theorem Complex.cos_eq_tsum' (z : ℂ) :
    Complex.cos z = ∑' n : ℕ, (z * Complex.I) ^ (2 * n) / ↑(2 * n)! :=
  (Complex.hasSum_cos' z).tsum_eq.symm

theorem Complex.sin_eq_tsum' (z : ℂ) :
    Complex.sin z = ∑' n : ℕ, (z * Complex.I) ^ (2 * n + 1) / ↑(2 * n + 1)! / Complex.I :=
  (Complex.hasSum_sin' z).tsum_eq.symm

theorem Complex.cos_eq_tsum (z : ℂ) :
    Complex.cos z = ∑' n : ℕ, (-1) ^ n * z ^ (2 * n) / ↑(2 * n)! :=
  (Complex.hasSum_cos z).tsum_eq.symm

theorem Complex.sin_eq_tsum (z : ℂ) :
    Complex.sin z = ∑' n : ℕ, (-1) ^ n * z ^ (2 * n + 1) / ↑(2 * n + 1)! :=
  (Complex.hasSum_sin z).tsum_eq.symm

/-- The power series expansion of `Real.cos`. -/
theorem Real.hasSum_cos (r : ℝ) :
    HasSum (fun n : ℕ => (-1) ^ n * r ^ (2 * n) / ↑(2 * n)!) (Real.cos r) :=
  mod_cast Complex.hasSum_cos r

/-- The power series expansion of `Real.sin`. -/
theorem Real.hasSum_sin (r : ℝ) :
    HasSum (fun n : ℕ => (-1) ^ n * r ^ (2 * n + 1) / ↑(2 * n + 1)!) (Real.sin r) :=
  mod_cast Complex.hasSum_sin r

theorem Real.cos_eq_tsum (r : ℝ) : Real.cos r = ∑' n : ℕ, (-1) ^ n * r ^ (2 * n) / ↑(2 * n)! :=
  (Real.hasSum_cos r).tsum_eq.symm

theorem Real.sin_eq_tsum (r : ℝ) :
    Real.sin r = ∑' n : ℕ, (-1) ^ n * r ^ (2 * n + 1) / ↑(2 * n + 1)! :=
  (Real.hasSum_sin r).tsum_eq.symm

end SinCos

/-! ### `cosh` and `sinh` for `ℝ` and `ℂ` -/

section SinhCosh
namespace Complex

/-- The power series expansion of `Complex.cosh`. -/
lemma hasSum_cosh (z : ℂ) : HasSum (fun n ↦ z ^ (2 * n) / ↑(2 * n)!) (cosh z) := by
  simpa [mul_assoc, cos_mul_I] using hasSum_cos' (z * I)

/-- The power series expansion of `Complex.sinh`. -/
lemma hasSum_sinh (z : ℂ) : HasSum (fun n ↦ z ^ (2 * n + 1) / ↑(2 * n + 1)!) (sinh z) := by
  simpa [mul_assoc, sin_mul_I, neg_pow z, pow_add, pow_mul, neg_mul, neg_div]
    using (hasSum_sin' (z * I)).mul_right (-I)

lemma cosh_eq_tsum (z : ℂ) : cosh z = ∑' n, z ^ (2 * n) / ↑(2 * n)! := z.hasSum_cosh.tsum_eq.symm

lemma sinh_eq_tsum (z : ℂ) : sinh z = ∑' n, z ^ (2 * n + 1) / ↑(2 * n + 1)! :=
  z.hasSum_sinh.tsum_eq.symm

end Complex

namespace Real

/-- The power series expansion of `Real.cosh`. -/
lemma hasSum_cosh (r : ℝ) : HasSum (fun n  ↦ r ^ (2 * n) / ↑(2 * n)!) (cosh r) :=
  mod_cast Complex.hasSum_cosh r

/-- The power series expansion of `Real.sinh`. -/
lemma hasSum_sinh (r : ℝ) : HasSum (fun n ↦ r ^ (2 * n + 1) / ↑(2 * n + 1)!) (sinh r) :=
  mod_cast Complex.hasSum_sinh r

lemma cosh_eq_tsum (r : ℝ) : cosh r = ∑' n, r ^ (2 * n) / ↑(2 * n)! := r.hasSum_cosh.tsum_eq.symm

lemma sinh_eq_tsum (r : ℝ) : sinh r = ∑' n, r ^ (2 * n + 1) / ↑(2 * n + 1)! :=
  r.hasSum_sinh.tsum_eq.symm

lemma cosh_le_exp_half_sq (x : ℝ) : cosh x ≤ exp (x ^ 2 / 2) := by
  rw [cosh_eq_tsum, exp_eq_exp_ℝ, exp_eq_tsum ℝ]
  refine x.hasSum_cosh.summable.tsum_le_tsum (fun i ↦ ?_) <| expSeries_summable' (x ^ 2 / 2)
  simp only [div_pow, pow_mul, smul_eq_mul, inv_mul_eq_div, div_div]
  gcongr
  norm_cast
  exact Nat.two_pow_mul_factorial_le_factorial_two_mul _

end Real
end SinhCosh
