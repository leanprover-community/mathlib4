/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Analysis.Quaternion
import Mathlib.Analysis.NormedSpace.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

#align_import analysis.normed_space.quaternion_exponential from "leanprover-community/mathlib"@"f0c8bf9245297a541f468be517f1bde6195105e9"

/-!
# Lemmas about `exp` on `Quaternion`s

This file contains results about `exp` on `Quaternion ℝ`.

## Main results

* `Quaternion.exp_eq`: the general expansion of the quaternion exponential in terms of `Real.cos`
  and `Real.sin`.
* `Quaternion.exp_of_re_eq_zero`: the special case when the quaternion has a zero real part.
* `Quaternion.norm_exp`: the norm of the quaternion exponential is the norm of the exponential of
  the real part.

-/


open scoped Quaternion Nat

namespace Quaternion

@[simp, norm_cast]
theorem exp_coe (r : ℝ) : exp ℝ (r : ℍ[ℝ]) = ↑(exp ℝ r) :=
  (map_exp ℝ (algebraMap ℝ ℍ[ℝ]) (continuous_algebraMap _ _) _).symm
#align quaternion.exp_coe Quaternion.exp_coe

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y) -- Porting note: See issue lean4#2220

/-- Auxiliary result; if the power series corresponding to `Real.cos` and `Real.sin` evaluated
at `‖q‖` tend to `c` and `s`, then the exponential series tends to `c + (s / ‖q‖)`. -/
theorem hasSum_expSeries_of_imaginary {q : Quaternion ℝ} (hq : q.re = 0) {c s : ℝ}
    (hc : HasSum (fun n => (-1 : ℝ) ^ n * ‖q‖ ^ (2 * n) / (2 * n)!) c)
    (hs : HasSum (fun n => (-1 : ℝ) ^ n * ‖q‖ ^ (2 * n + 1) / (2 * n + 1)!) s) :
    HasSum (fun n => expSeries ℝ (Quaternion ℝ) n fun _ => q) (↑c + (s / ‖q‖) • q) := by
  replace hc := hasSum_coe.mpr hc
  -- ⊢ HasSum (fun n => ↑(expSeries ℝ ℍ n) fun x => q) (↑c + (s / ‖q‖) • q)
  replace hs := (hs.div_const ‖q‖).smul_const q
  -- ⊢ HasSum (fun n => ↑(expSeries ℝ ℍ n) fun x => q) (↑c + (s / ‖q‖) • q)
  obtain rfl | hq0 := eq_or_ne q 0
  -- ⊢ HasSum (fun n => ↑(expSeries ℝ ℍ n) fun x => 0) (↑c + (s / ‖0‖) • 0)
  · simp_rw [expSeries_apply_zero, norm_zero, div_zero, zero_smul, add_zero]
    -- ⊢ HasSum (fun n => Pi.single 0 1 n) ↑c
    simp_rw [norm_zero] at hc
    -- ⊢ HasSum (fun n => Pi.single 0 1 n) ↑c
    convert hc using 1
    -- ⊢ (fun n => Pi.single 0 1 n) = fun a => ↑((-1) ^ a * 0 ^ (2 * a) / ↑(2 * a)!)
    ext (_ | n) : 1
    -- ⊢ Pi.single 0 1 Nat.zero = ↑((-1) ^ Nat.zero * 0 ^ (2 * Nat.zero) / ↑(2 * Nat. …
    · rw [pow_zero, Nat.zero_eq, mul_zero, pow_zero, Nat.factorial_zero, Nat.cast_one,
        div_one, one_mul, Pi.single_eq_same, coe_one]
    · rw [zero_pow (mul_pos two_pos (Nat.succ_pos _)), mul_zero, zero_div,
        Pi.single_eq_of_ne n.succ_ne_zero, coe_zero]
  simp_rw [expSeries_apply_eq]
  -- ⊢ HasSum (fun n => (↑n !)⁻¹ • q ^ n) (↑c + (s / ‖q‖) • q)
  have hq2 : q ^ 2 = -normSq q := sq_eq_neg_normSq.mpr hq
  -- ⊢ HasSum (fun n => (↑n !)⁻¹ • q ^ n) (↑c + (s / ‖q‖) • q)
  have hqn := norm_ne_zero_iff.mpr hq0
  -- ⊢ HasSum (fun n => (↑n !)⁻¹ • q ^ n) (↑c + (s / ‖q‖) • q)
  refine' HasSum.even_add_odd _ _
  -- ⊢ HasSum (fun k => (↑(2 * k)!)⁻¹ • q ^ (2 * k)) ↑c
  · convert hc using 1
    -- ⊢ (fun k => (↑(2 * k)!)⁻¹ • q ^ (2 * k)) = fun a => ↑((-1) ^ a * ‖q‖ ^ (2 * a) …
    ext n : 1
    -- ⊢ (↑(2 * n)!)⁻¹ • q ^ (2 * n) = ↑((-1) ^ n * ‖q‖ ^ (2 * n) / ↑(2 * n)!)
    letI k : ℝ := ↑(2 * n)!
    -- ⊢ (↑(2 * n)!)⁻¹ • q ^ (2 * n) = ↑((-1) ^ n * ‖q‖ ^ (2 * n) / ↑(2 * n)!)
    calc
      k⁻¹ • q ^ (2 * n) = k⁻¹ • (-normSq q) ^ n := by rw [pow_mul, hq2]; norm_cast
      _ = k⁻¹ • ↑((-1 : ℝ) ^ n * ‖q‖ ^ (2 * n)) := ?_
      _ = ↑((-1 : ℝ) ^ n * ‖q‖ ^ (2 * n) / k) := ?_
    · congr 1
      -- ⊢ ↑(k⁻¹ • (-↑normSq q) ^ n) = k⁻¹ • ↑((-1) ^ n * ‖q‖ ^ (2 * n))
      rw [neg_pow, normSq_eq_norm_mul_self, pow_mul, sq]
      -- ⊢ ↑(k⁻¹ • ((-1) ^ n * (‖q‖ * ‖q‖) ^ n)) = k⁻¹ • ↑((-1) ^ n * (‖q‖ * ‖q‖) ^ n)
      push_cast
      -- ⊢ (↑(2 * n)!)⁻¹ • ((-1) ^ n * (↑‖q‖ * ↑‖q‖) ^ n) = (↑(2 * n)!)⁻¹ • ((-1) ^ n * …
      rfl
      -- 🎉 no goals
    · rw [← coe_mul_eq_smul, div_eq_mul_inv]
      -- ⊢ ↑k⁻¹ * ↑((-1) ^ n * ‖q‖ ^ (2 * n)) = ↑((-1) ^ n * ‖q‖ ^ (2 * n) * k⁻¹)
      norm_cast
      -- ⊢ ↑(k⁻¹ * (↑(Int.negSucc 0 ^ n) * ‖q‖ ^ (2 * n))) = ↑(↑(Int.negSucc 0 ^ n) * ‖ …
      ring_nf
      -- 🎉 no goals
  · convert hs using 1
    -- ⊢ (fun k => (↑(2 * k + 1)!)⁻¹ • q ^ (2 * k + 1)) = fun z => ((-1) ^ z * ‖q‖ ^  …
    ext n : 1
    -- ⊢ (↑(2 * n + 1)!)⁻¹ • q ^ (2 * n + 1) = ((-1) ^ n * ‖q‖ ^ (2 * n + 1) / ↑(2 *  …
    let k : ℝ := ↑(2 * n + 1)!
    -- ⊢ (↑(2 * n + 1)!)⁻¹ • q ^ (2 * n + 1) = ((-1) ^ n * ‖q‖ ^ (2 * n + 1) / ↑(2 *  …
    calc
      k⁻¹ • q ^ (2 * n + 1) = k⁻¹ • ((-normSq q) ^ n * q) := by
        rw [pow_succ', pow_mul, hq2]
        norm_cast
      _ = k⁻¹ • ((-1 : ℝ) ^ n * ‖q‖ ^ (2 * n)) • q := ?_
      _ = ((-1 : ℝ) ^ n * ‖q‖ ^ (2 * n + 1) / k / ‖q‖) • q := ?_
    · congr 1
      -- ⊢ ↑((-↑normSq q) ^ n) * q = ((-1) ^ n * ‖q‖ ^ (2 * n)) • q
      rw [neg_pow, normSq_eq_norm_mul_self, pow_mul, sq, ← coe_mul_eq_smul]
      -- 🎉 no goals
    · rw [smul_smul]
      -- ⊢ (k⁻¹ * ((-1) ^ n * ‖q‖ ^ (2 * n))) • q = ((-1) ^ n * ‖q‖ ^ (2 * n + 1) / k / …
      congr 1
      -- ⊢ k⁻¹ * ((-1) ^ n * ‖q‖ ^ (2 * n)) = (-1) ^ n * ‖q‖ ^ (2 * n + 1) / k / ‖q‖
      simp_rw [pow_succ', mul_div_assoc, div_div_cancel_left' hqn]
      -- ⊢ (↑(2 * n + 1)!)⁻¹ * ((-1) ^ n * ‖q‖ ^ (2 * n)) = (-1) ^ n * (‖q‖ ^ (2 * n) * …
      ring
      -- 🎉 no goals
#align quaternion.has_sum_exp_series_of_imaginary Quaternion.hasSum_expSeries_of_imaginary

/-- The closed form for the quaternion exponential on imaginary quaternions. -/
theorem exp_of_re_eq_zero (q : Quaternion ℝ) (hq : q.re = 0) :
    exp ℝ q = ↑(Real.cos ‖q‖) + (Real.sin ‖q‖ / ‖q‖) • q := by
  rw [exp_eq_tsum]
  -- ⊢ (fun x => ∑' (n : ℕ), (↑n !)⁻¹ • x ^ n) q = ↑(Real.cos ‖q‖) + (Real.sin ‖q‖  …
  refine' HasSum.tsum_eq _
  -- ⊢ HasSum (fun n => (↑n !)⁻¹ • q ^ n) (↑(Real.cos ‖q‖) + (Real.sin ‖q‖ / ‖q‖) • …
  simp_rw [← expSeries_apply_eq]
  -- ⊢ HasSum (fun n => ↑(expSeries ℝ ℍ n) fun x => q) (↑(Real.cos ‖q‖) + (Real.sin …
  exact hasSum_expSeries_of_imaginary hq (Real.hasSum_cos _) (Real.hasSum_sin _)
  -- 🎉 no goals
#align quaternion.exp_of_re_eq_zero Quaternion.exp_of_re_eq_zero

/-- The closed form for the quaternion exponential on arbitrary quaternions. -/
theorem exp_eq (q : Quaternion ℝ) :
    exp ℝ q = exp ℝ q.re • (↑(Real.cos ‖q.im‖) + (Real.sin ‖q.im‖ / ‖q.im‖) • q.im) := by
  rw [← exp_of_re_eq_zero q.im q.im_re, ← coe_mul_eq_smul, ← exp_coe, ← exp_add_of_commute,
    re_add_im]
  exact Algebra.commutes q.re (_ : ℍ[ℝ])
  -- 🎉 no goals
#align quaternion.exp_eq Quaternion.exp_eq

theorem re_exp (q : ℍ[ℝ]) : (exp ℝ q).re = exp ℝ q.re * Real.cos ‖q - q.re‖ := by simp [exp_eq]
                                                                                  -- 🎉 no goals
#align quaternion.re_exp Quaternion.re_exp

theorem im_exp (q : ℍ[ℝ]) : (exp ℝ q).im = (exp ℝ q.re * (Real.sin ‖q.im‖ / ‖q.im‖)) • q.im := by
  simp [exp_eq, smul_smul]
  -- 🎉 no goals
#align quaternion.im_exp Quaternion.im_exp

theorem normSq_exp (q : ℍ[ℝ]) : normSq (exp ℝ q) = exp ℝ q.re ^ 2 :=
  calc
    normSq (exp ℝ q) =
        normSq (exp ℝ q.re • (↑(Real.cos ‖q.im‖) + (Real.sin ‖q.im‖ / ‖q.im‖) • q.im)) :=
      by rw [exp_eq]
         -- 🎉 no goals
    _ = exp ℝ q.re ^ 2 * normSq (↑(Real.cos ‖q.im‖) + (Real.sin ‖q.im‖ / ‖q.im‖) • q.im) := by
      rw [normSq_smul]
      -- 🎉 no goals
    _ = exp ℝ q.re ^ 2 * (Real.cos ‖q.im‖ ^ 2 + Real.sin ‖q.im‖ ^ 2) := by
      congr 1
      -- ⊢ ↑normSq (↑(Real.cos ‖im q‖) + (Real.sin ‖im q‖ / ‖im q‖) • im q) = Real.cos  …
      obtain hv | hv := eq_or_ne ‖q.im‖ 0
      -- ⊢ ↑normSq (↑(Real.cos ‖im q‖) + (Real.sin ‖im q‖ / ‖im q‖) • im q) = Real.cos  …
      · simp [hv]
        -- 🎉 no goals
      rw [normSq_add, normSq_smul, star_smul, coe_mul_eq_smul, smul_re, smul_re, star_re, im_re,
        smul_zero, smul_zero, mul_zero, add_zero, div_pow, normSq_coe,
        normSq_eq_norm_mul_self, ← sq, div_mul_cancel _ (pow_ne_zero _ hv)]
    _ = exp ℝ q.re ^ 2 := by rw [Real.cos_sq_add_sin_sq, mul_one]
                             -- 🎉 no goals

#align quaternion.norm_sq_exp Quaternion.normSq_exp

/-- Note that this implies that exponentials of pure imaginary quaternions are unit quaternions
since in that case the RHS is `1` via `exp_zero` and `norm_one`. -/
@[simp]
theorem norm_exp (q : ℍ[ℝ]) : ‖exp ℝ q‖ = ‖exp ℝ q.re‖ := by
  rw [norm_eq_sqrt_real_inner (exp ℝ q), inner_self, normSq_exp, Real.sqrt_sq_eq_abs,
    Real.norm_eq_abs]
#align quaternion.norm_exp Quaternion.norm_exp

end Quaternion
