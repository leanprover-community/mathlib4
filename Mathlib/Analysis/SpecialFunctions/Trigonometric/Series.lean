/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Analysis.SpecialFunctions.Exponential

#align_import analysis.special_functions.trigonometric.series from "leanprover-community/mathlib"@"ccf84e0d918668460a34aa19d02fe2e0e2286da0"

/-!
# Trigonometric functions as sums of infinite series

In this file we express trigonometric functions in terms of their series expansion.

## Main results

* `Complex.hasSum_cos`, `Complex.cos_eq_tsum`: `Complex.cos` as the sum of an infinite series.
* `Real.hasSum_cos`, `Real.cos_eq_tsum`: `Real.cos` as the sum of an infinite series.
* `Complex.hasSum_sin`, `Complex.sin_eq_tsum`: `Complex.sin` as the sum of an infinite series.
* `Real.hasSum_sin`, `Real.sin_eq_tsum`: `Real.sin` as the sum of an infinite series.
-/


open scoped Nat

/-! ### `cos` and `sin` for `ℝ` and `ℂ` -/


section SinCos

theorem Complex.hasSum_cos' (z : ℂ) :
    HasSum (fun n : ℕ => (z * Complex.I) ^ (2 * n) / ↑(2 * n)!) (Complex.cos z) := by
  rw [Complex.cos, Complex.exp_eq_exp_ℂ]
  -- ⊢ HasSum (fun n => (z * I) ^ (2 * n) / ↑(2 * n)!) ((_root_.exp ℂ (z * I) + _ro …
  have := ((expSeries_div_hasSum_exp ℂ (z * Complex.I)).add
    (expSeries_div_hasSum_exp ℂ (-z * Complex.I))).div_const 2
  replace := (Nat.divModEquiv 2).symm.hasSum_iff.mpr this
  -- ⊢ HasSum (fun n => (z * I) ^ (2 * n) / ↑(2 * n)!) ((_root_.exp ℂ (z * I) + _ro …
  dsimp [Function.comp] at this
  -- ⊢ HasSum (fun n => (z * I) ^ (2 * n) / ↑(2 * n)!) ((_root_.exp ℂ (z * I) + _ro …
  simp_rw [← mul_comm 2 _] at this
  -- ⊢ HasSum (fun n => (z * I) ^ (2 * n) / ↑(2 * n)!) ((_root_.exp ℂ (z * I) + _ro …
  refine' this.prod_fiberwise fun k => _
  -- ⊢ HasSum (fun c => ((z * I) ^ (2 * (k, c).fst + ↑(k, c).snd) / ↑(2 * (k, c).fs …
  dsimp only
  -- ⊢ HasSum (fun c => ((z * I) ^ (2 * k + ↑c) / ↑(2 * k + ↑c)! + (-z * I) ^ (2 *  …
  convert hasSum_fintype (_ : Fin 2 → ℂ) using 1
  -- ⊢ (z * I) ^ (2 * k) / ↑(2 * k)! = Finset.sum Finset.univ fun b => ((z * I) ^ ( …
  rw [Fin.sum_univ_two]
  -- ⊢ (z * I) ^ (2 * k) / ↑(2 * k)! = ((z * I) ^ (2 * k + ↑0) / ↑(2 * k + ↑0)! + ( …
  simp_rw [Fin.val_zero, Fin.val_one, add_zero, pow_succ', pow_mul, mul_pow, neg_sq, ← two_mul,
    neg_mul, mul_neg, neg_div, add_right_neg, zero_div, add_zero,
    mul_div_cancel_left _ (two_ne_zero : (2 : ℂ) ≠ 0)]
#align complex.has_sum_cos' Complex.hasSum_cos'

theorem Complex.hasSum_sin' (z : ℂ) :
    HasSum (fun n : ℕ => (z * Complex.I) ^ (2 * n + 1) / ↑(2 * n + 1)! / Complex.I)
      (Complex.sin z) := by
  rw [Complex.sin, Complex.exp_eq_exp_ℂ]
  -- ⊢ HasSum (fun n => (z * I) ^ (2 * n + 1) / ↑(2 * n + 1)! / I) ((_root_.exp ℂ ( …
  have := (((expSeries_div_hasSum_exp ℂ (-z * Complex.I)).sub
    (expSeries_div_hasSum_exp ℂ (z * Complex.I))).mul_right Complex.I).div_const 2
  replace := (Nat.divModEquiv 2).symm.hasSum_iff.mpr this
  -- ⊢ HasSum (fun n => (z * I) ^ (2 * n + 1) / ↑(2 * n + 1)! / I) ((_root_.exp ℂ ( …
  dsimp [Function.comp] at this
  -- ⊢ HasSum (fun n => (z * I) ^ (2 * n + 1) / ↑(2 * n + 1)! / I) ((_root_.exp ℂ ( …
  simp_rw [← mul_comm 2 _] at this
  -- ⊢ HasSum (fun n => (z * I) ^ (2 * n + 1) / ↑(2 * n + 1)! / I) ((_root_.exp ℂ ( …
  refine' this.prod_fiberwise fun k => _
  -- ⊢ HasSum (fun c => ((-z * I) ^ (2 * (k, c).fst + ↑(k, c).snd) / ↑(2 * (k, c).f …
  dsimp only
  -- ⊢ HasSum (fun c => ((-z * I) ^ (2 * k + ↑c) / ↑(2 * k + ↑c)! - (z * I) ^ (2 *  …
  convert hasSum_fintype (_ : Fin 2 → ℂ) using 1
  -- ⊢ (z * I) ^ (2 * k + 1) / ↑(2 * k + 1)! / I = Finset.sum Finset.univ fun b =>  …
  rw [Fin.sum_univ_two]
  -- ⊢ (z * I) ^ (2 * k + 1) / ↑(2 * k + 1)! / I = ((-z * I) ^ (2 * k + ↑0) / ↑(2 * …
  simp_rw [Fin.val_zero, Fin.val_one, add_zero, pow_succ', pow_mul, mul_pow, neg_sq, sub_self,
    zero_mul, zero_div, zero_add, neg_mul, mul_neg, neg_div, ← neg_add', ← two_mul,
    neg_mul, neg_div, mul_assoc, mul_div_cancel_left _ (two_ne_zero : (2 : ℂ) ≠ 0), Complex.div_I]
#align complex.has_sum_sin' Complex.hasSum_sin'

/-- The power series expansion of `Complex.cos`. -/
theorem Complex.hasSum_cos (z : ℂ) :
    HasSum (fun n : ℕ => (-1) ^ n * z ^ (2 * n) / ↑(2 * n)!) (Complex.cos z) := by
  convert Complex.hasSum_cos' z using 1
  -- ⊢ (fun n => (-1) ^ n * z ^ (2 * n) / ↑(2 * n)!) = fun n => (z * I) ^ (2 * n) / …
  simp_rw [mul_pow, pow_mul, Complex.I_sq, mul_comm]
  -- 🎉 no goals
#align complex.has_sum_cos Complex.hasSum_cos

/-- The power series expansion of `Complex.sin`. -/
theorem Complex.hasSum_sin (z : ℂ) :
    HasSum (fun n : ℕ => (-1) ^ n * z ^ (2 * n + 1) / ↑(2 * n + 1)!) (Complex.sin z) := by
  convert Complex.hasSum_sin' z using 1
  -- ⊢ (fun n => (-1) ^ n * z ^ (2 * n + 1) / ↑(2 * n + 1)!) = fun n => (z * I) ^ ( …
  simp_rw [mul_pow, pow_succ', pow_mul, Complex.I_sq, ← mul_assoc, mul_div_assoc, div_right_comm,
    div_self Complex.I_ne_zero, mul_comm _ ((-1 : ℂ) ^ _), mul_one_div, mul_div_assoc, mul_assoc]
#align complex.has_sum_sin Complex.hasSum_sin

theorem Complex.cos_eq_tsum' (z : ℂ) :
    Complex.cos z = ∑' n : ℕ, (z * Complex.I) ^ (2 * n) / ↑(2 * n)! :=
  (Complex.hasSum_cos' z).tsum_eq.symm
#align complex.cos_eq_tsum' Complex.cos_eq_tsum'

theorem Complex.sin_eq_tsum' (z : ℂ) :
    Complex.sin z = ∑' n : ℕ, (z * Complex.I) ^ (2 * n + 1) / ↑(2 * n + 1)! / Complex.I :=
  (Complex.hasSum_sin' z).tsum_eq.symm
#align complex.sin_eq_tsum' Complex.sin_eq_tsum'

theorem Complex.cos_eq_tsum (z : ℂ) :
    Complex.cos z = ∑' n : ℕ, (-1) ^ n * z ^ (2 * n) / ↑(2 * n)! :=
  (Complex.hasSum_cos z).tsum_eq.symm
#align complex.cos_eq_tsum Complex.cos_eq_tsum

theorem Complex.sin_eq_tsum (z : ℂ) :
    Complex.sin z = ∑' n : ℕ, (-1) ^ n * z ^ (2 * n + 1) / ↑(2 * n + 1)! :=
  (Complex.hasSum_sin z).tsum_eq.symm
#align complex.sin_eq_tsum Complex.sin_eq_tsum

/-- The power series expansion of `Real.cos`. -/
theorem Real.hasSum_cos (r : ℝ) :
    HasSum (fun n : ℕ => (-1) ^ n * r ^ (2 * n) / ↑(2 * n)!) (Real.cos r) := by
  exact_mod_cast Complex.hasSum_cos r
  -- 🎉 no goals
#align real.has_sum_cos Real.hasSum_cos

/-- The power series expansion of `Real.sin`. -/
theorem Real.hasSum_sin (r : ℝ) :
    HasSum (fun n : ℕ => (-1) ^ n * r ^ (2 * n + 1) / ↑(2 * n + 1)!) (Real.sin r) := by
  exact_mod_cast Complex.hasSum_sin r
  -- 🎉 no goals
#align real.has_sum_sin Real.hasSum_sin

theorem Real.cos_eq_tsum (r : ℝ) : Real.cos r = ∑' n : ℕ, (-1) ^ n * r ^ (2 * n) / ↑(2 * n)! :=
  (Real.hasSum_cos r).tsum_eq.symm
#align real.cos_eq_tsum Real.cos_eq_tsum

theorem Real.sin_eq_tsum (r : ℝ) :
    Real.sin r = ∑' n : ℕ, (-1) ^ n * r ^ (2 * n + 1) / ↑(2 * n + 1)! :=
  (Real.hasSum_sin r).tsum_eq.symm
#align real.sin_eq_tsum Real.sin_eq_tsum

end SinCos
