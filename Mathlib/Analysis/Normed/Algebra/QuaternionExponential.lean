/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Analysis.Quaternion
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-!
# Lemmas about `NormedSpace.exp` on `Quaternion`s

This file contains results about `NormedSpace.exp` on `Quaternion ℝ`.

## Main results

* `Quaternion.exp_eq`: the general expansion of the quaternion exponential in terms of `Real.cos`
  and `Real.sin`.
* `Quaternion.exp_of_re_eq_zero`: the special case when the quaternion has a zero real part.
* `Quaternion.norm_exp`: the norm of the quaternion exponential is the norm of the exponential of
  the real part.

-/

open scoped Quaternion Nat

open NormedSpace

namespace Quaternion

@[simp, norm_cast]
theorem exp_coe (r : ℝ) : exp ℝ (r : ℍ[ℝ]) = ↑(exp ℝ r) :=
  (map_exp ℝ (algebraMap ℝ ℍ[ℝ]) (continuous_algebraMap _ _) _).symm

/-- The even terms of `expSeries` are real, and correspond to the series for $\cos ‖q‖$. -/
theorem expSeries_even_of_imaginary {q : Quaternion ℝ} (hq : q.re = 0) (n : ℕ) :
    expSeries ℝ (Quaternion ℝ) (2 * n) (fun _ => q) =
      ↑((-1 : ℝ) ^ n * ‖q‖ ^ (2 * n) / (2 * n)!) := by
  rw [expSeries_apply_eq]
  have hq2 : q ^ 2 = -normSq q := sq_eq_neg_normSq.mpr hq
  letI k : ℝ := ↑(2 * n)!
  calc
    k⁻¹ • q ^ (2 * n) = k⁻¹ • (-normSq q) ^ n := by rw [pow_mul, hq2]
    _ = k⁻¹ • ↑((-1 : ℝ) ^ n * ‖q‖ ^ (2 * n)) := ?_
    _ = ↑((-1 : ℝ) ^ n * ‖q‖ ^ (2 * n) / k) := ?_
  · congr 1
    rw [neg_pow, normSq_eq_norm_mul_self, pow_mul, sq]
    push_cast
    rfl
  · rw [← coe_mul_eq_smul, div_eq_mul_inv]
    norm_cast
    ring_nf

/-- The odd terms of `expSeries` are real, and correspond to the series for
$\frac{q}{‖q‖} \sin ‖q‖$. -/
theorem expSeries_odd_of_imaginary {q : Quaternion ℝ} (hq : q.re = 0) (n : ℕ) :
    expSeries ℝ (Quaternion ℝ) (2 * n + 1) (fun _ => q) =
      (((-1 : ℝ) ^ n * ‖q‖ ^ (2 * n + 1) / (2 * n + 1)!) / ‖q‖) • q := by
  rw [expSeries_apply_eq]
  obtain rfl | hq0 := eq_or_ne q 0
  · simp
  have hq2 : q ^ 2 = -normSq q := sq_eq_neg_normSq.mpr hq
  have hqn := norm_ne_zero_iff.mpr hq0
  let k : ℝ := ↑(2 * n + 1)!
  calc
    k⁻¹ • q ^ (2 * n + 1) = k⁻¹ • ((-normSq q) ^ n * q) := by rw [pow_succ, pow_mul, hq2]
    _ = k⁻¹ • ((-1 : ℝ) ^ n * ‖q‖ ^ (2 * n)) • q := ?_
    _ = ((-1 : ℝ) ^ n * ‖q‖ ^ (2 * n + 1) / k / ‖q‖) • q := ?_
  · congr 1
    rw [neg_pow, normSq_eq_norm_mul_self, pow_mul, sq, ← coe_mul_eq_smul]
    norm_cast
  · rw [smul_smul]
    congr 1
    simp_rw [pow_succ, mul_div_assoc, div_div_cancel_left' hqn]
    ring

/-- Auxiliary result; if the power series corresponding to `Real.cos` and `Real.sin` evaluated
at `‖q‖` tend to `c` and `s`, then the exponential series tends to `c + (s / ‖q‖)`. -/
theorem hasSum_expSeries_of_imaginary {q : Quaternion ℝ} (hq : q.re = 0) {c s : ℝ}
    (hc : HasSum (fun n => (-1 : ℝ) ^ n * ‖q‖ ^ (2 * n) / (2 * n)!) c)
    (hs : HasSum (fun n => (-1 : ℝ) ^ n * ‖q‖ ^ (2 * n + 1) / (2 * n + 1)!) s) :
    HasSum (fun n => expSeries ℝ (Quaternion ℝ) n fun _ => q) (↑c + (s / ‖q‖) • q) := by
  replace hc := hasSum_coe.mpr hc
  replace hs := (hs.div_const ‖q‖).smul_const q
  refine HasSum.even_add_odd ?_ ?_
  · convert hc using 1
    ext n : 1
    rw [expSeries_even_of_imaginary hq]
  · convert hs using 1
    ext n : 1
    rw [expSeries_odd_of_imaginary hq]

/-- The closed form for the quaternion exponential on imaginary quaternions. -/
theorem exp_of_re_eq_zero (q : Quaternion ℝ) (hq : q.re = 0) :
    exp ℝ q = ↑(Real.cos ‖q‖) + (Real.sin ‖q‖ / ‖q‖) • q := by
  rw [exp_eq_tsum]
  refine HasSum.tsum_eq ?_
  simp_rw [← expSeries_apply_eq]
  exact hasSum_expSeries_of_imaginary hq (Real.hasSum_cos _) (Real.hasSum_sin _)

/-- The closed form for the quaternion exponential on arbitrary quaternions. -/
theorem exp_eq (q : Quaternion ℝ) :
    exp ℝ q = exp ℝ q.re • (↑(Real.cos ‖q.im‖) + (Real.sin ‖q.im‖ / ‖q.im‖) • q.im) := by
  rw [← exp_of_re_eq_zero q.im q.re_im, ← coe_mul_eq_smul, ← exp_coe, ← exp_add_of_commute,
    re_add_im]
  exact Algebra.commutes q.re (_ : ℍ[ℝ])

theorem re_exp (q : ℍ[ℝ]) : (exp ℝ q).re = exp ℝ q.re * Real.cos ‖q - q.re‖ := by simp [exp_eq]

theorem im_exp (q : ℍ[ℝ]) : (exp ℝ q).im = (exp ℝ q.re * (Real.sin ‖q.im‖ / ‖q.im‖)) • q.im := by
  simp [exp_eq, smul_smul]

theorem normSq_exp (q : ℍ[ℝ]) : normSq (exp ℝ q) = exp ℝ q.re ^ 2 :=
  calc
    normSq (exp ℝ q) =
        normSq (exp ℝ q.re • (↑(Real.cos ‖q.im‖) + (Real.sin ‖q.im‖ / ‖q.im‖) • q.im)) := by
      rw [exp_eq]
    _ = exp ℝ q.re ^ 2 * normSq (↑(Real.cos ‖q.im‖) + (Real.sin ‖q.im‖ / ‖q.im‖) • q.im) := by
      rw [normSq_smul]
    _ = exp ℝ q.re ^ 2 * (Real.cos ‖q.im‖ ^ 2 + Real.sin ‖q.im‖ ^ 2) := by
      congr 1
      obtain hv | hv := eq_or_ne ‖q.im‖ 0
      · simp [hv]
      rw [normSq_add, normSq_smul, star_smul, coe_mul_eq_smul, re_smul, re_smul, re_star, re_im,
        smul_zero, smul_zero, mul_zero, add_zero, div_pow, normSq_coe,
        normSq_eq_norm_mul_self, ← sq, div_mul_cancel₀ _ (pow_ne_zero _ hv)]
    _ = exp ℝ q.re ^ 2 := by rw [Real.cos_sq_add_sin_sq, mul_one]

/-- Note that this implies that exponentials of pure imaginary quaternions are unit quaternions
since in that case the RHS is `1` via `NormedSpace.exp_zero` and `norm_one`. -/
@[simp]
theorem norm_exp (q : ℍ[ℝ]) : ‖exp ℝ q‖ = ‖exp ℝ q.re‖ := by
  rw [norm_eq_sqrt_real_inner (exp ℝ q), inner_self, normSq_exp, Real.sqrt_sq_eq_abs,
    Real.norm_eq_abs]

end Quaternion
