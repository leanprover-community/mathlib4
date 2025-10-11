/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.Analysis.Complex.TaylorSeries

/-!
# Taylor expansion of `1 / z ^ r`
-/

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

lemma deriv_div_sub_pow (z w a : 𝕜) (r : ℕ) :
    deriv (fun z : 𝕜 ↦ a / (w - z) ^ r) z = r * a / (w - z) ^ (r + 1) := by
  rw [deriv_comp_const_sub (f := fun z ↦ a / z ^ r) (a := w)]
  simp [div_eq_mul_inv, deriv_const_mul_field', ← zpow_natCast, ← zpow_neg,
    deriv_zpow, neg_add_eq_sub, mul_assoc, mul_left_comm _ a]

lemma hasDerivAt_div_sub_pow (z w a : 𝕜) (r : ℕ) (hz : z ≠ w) :
    HasDerivAt (fun z : 𝕜 ↦ a / (w - z) ^ r) (r * a / (w - z) ^ (r + 1)) z := by
  rw [← deriv_div_sub_pow, hasDerivAt_deriv_iff]
  refine .div (by fun_prop) (by fun_prop) (by simp [eq_comm, sub_eq_zero, hz])

lemma iter_deriv_div_sub_pow (z w a : 𝕜) (r k : ℕ) :
    deriv^[k] (fun z : 𝕜 ↦ a / (w - z) ^ r) z = r.ascFactorial k * a / (w - z) ^ (r + k) := by
  revert z
  apply funext_iff.mp
  induction k with
  | zero => simp
  | succ k IH =>
    ext z
    simp [Function.iterate_succ', IH, deriv_div_sub_pow, Nat.ascFactorial_succ,
      ← add_assoc, mul_assoc, -Function.iterate_succ]

/-- Taylor expansion of `1 / z ^ k` at `w`. -/
lemma Complex.tsum_eq_one_div_sub_pow (w z : ℂ) (hz : ‖z‖ < ‖w‖) (k : ℕ) (hk : k ≠ 0) :
    ∑' i : ℕ, (Nat.choose (i + k - 1) i) * w ^ (- ↑(i + k) : ℤ) * z ^ i = 1 / (w - z) ^ k := by
  convert Complex.taylorSeries_eq_on_ball' (f := fun z ↦ 1 / (w - z) ^ k)
    (show z ∈ Metric.ball 0 ‖w‖ by simpa using hz) _ using 4 with i
  · rw [iteratedDeriv_eq_iterate, iter_deriv_div_sub_pow, sub_zero, zpow_neg, zpow_natCast, mul_one,
      eq_inv_mul_iff_mul_eq₀ (by norm_cast; positivity), ← mul_assoc, div_eq_mul_inv, add_comm,
      ← Nat.cast_mul, Nat.ascFactorial_eq_factorial_mul_choose']
  · simp
  · exact .div (by fun_prop) (by fun_prop) (by simp [sub_eq_zero, imp_not_comm, hk])

/-- Taylor expansion of `1 / z ^ k` at `w`. -/
lemma Complex.hasSum_one_div_sub_pow (w z : ℂ) (hz : ‖z‖ < ‖w‖) (k : ℕ) (hk : k ≠ 0) :
    HasSum (fun i ↦ (Nat.choose (i + k - 1) i) * w ^ (- ↑(i + k) : ℤ) * z ^ i)
      (1 / (w - z) ^ k) := by
  rw [Summable.hasSum_iff, tsum_eq_one_div_sub_pow w z hz k hk]
  by_contra H
  obtain ⟨rfl, -⟩ : w = z ∧ k ≠ 0 := by simpa [sub_eq_zero] using
    (tsum_eq_one_div_sub_pow w z hz k hk).symm.trans (tsum_eq_zero_of_not_summable H)
  simp at hz

/-- Taylor expansion of `1 / z` at `w`. -/
lemma Complex.tsum_eq_one_div_sub (w z : ℂ) (hz : ‖z‖ < ‖w‖) :
    ∑' i : ℕ, w ^ (- ↑(i + 1) : ℤ) * z ^ i = 1 / (w - z) := by
  convert tsum_eq_one_div_sub_pow w z hz 1 one_ne_zero <;> simp

/-- Taylor expansion of `1 / z ^ 2` at `w`. -/
lemma Complex.tsum_eq_one_div_sub_sq (w z : ℂ) (hz : ‖z‖ < ‖w‖) :
    ∑' i : ℕ, (i + 1) * w ^ (- ↑(i + 2) : ℤ) * z ^ i = 1 / (w - z) ^ 2 := by
  convert tsum_eq_one_div_sub_pow w z hz 2 two_ne_zero; simp

/-- `∑ (ai + b)zⁱ = (b - a) / (1 - z) + a / (1 - z)²` -/
lemma Complex.tsum_mul_add_const_mul_pow (z a b : ℂ) (hz : ‖z‖ < 1) :
    ∑' i : ℕ, (a * i + b) * z ^ i = (b - a) / (1 - z) + a / (1 - z) ^ 2 := by
  have H : ‖z‖ < ‖(1 : ℂ)‖ := by simpa using hz
  simp_rw [div_eq_mul_inv, ← one_div]
  rw [← Complex.tsum_eq_one_div_sub_sq _ _ H, ← Complex.tsum_eq_one_div_sub _ _ H, ← tsum_mul_left,
    ← tsum_mul_left, ← Summable.tsum_add]
  · congr 1 with i
    simp
    ring
  · refine .mul_left _ ?_
    by_contra h
    obtain rfl : 1 = z := by simpa [sub_eq_zero] using
      (tsum_eq_one_div_sub _ _ H).symm.trans (tsum_eq_zero_of_not_summable h)
    simp at hz
  · refine .mul_left _ ?_
    by_contra h
    obtain rfl : 1 = z := by simpa [sub_eq_zero] using
      (tsum_eq_one_div_sub_sq _ _ H).symm.trans (tsum_eq_zero_of_not_summable h)
    simp at hz

lemma Real.tsum_eq_one_div_sub_sq (w z : ℝ) (hz : |z| < |w|) :
    ∑' i : ℕ, (i + 1) * w ^ (- ↑(i + 2) : ℤ) * z ^ i = 1 / (w - z) ^ 2 := by
  exact_mod_cast Complex.tsum_eq_one_div_sub_sq w z (by simpa)

lemma Real.tsum_mul_add_const_mul_pow (a b z : ℝ) (hz : |z| < 1) :
    ∑' i : ℕ, (a * i + b) * z ^ i = (b - a) / (1 - z) + a / (1 - z) ^ 2 := by
  exact_mod_cast Complex.tsum_mul_add_const_mul_pow z a b (by simpa)
