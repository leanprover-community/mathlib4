/-
Copyright (c) 2021 Benjamin Davidson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Davidson
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.SpecialFunctions.NonIntegrable
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Integration of specific interval integrals

This file contains proofs of the integrals of various specific functions. This includes:
* Integrals of simple functions, such as `id`, `pow`, `inv`, `exp`, `log`
* Integrals of some trigonometric functions, such as `sin`, `cos`, `1 / (1 + x^2)`
* The integral of `cos x ^ 2 - sin x ^ 2`
* Reduction formulae for the integrals of `sin x ^ n` and `cos x ^ n` for `n ≥ 2`
* The computation of `∫ x in 0..π, sin x ^ n` as a product for even and odd `n` (used in proving the
  Wallis product for pi)
* Integrals of the form `sin x ^ m * cos x ^ n`

With these lemmas, many simple integrals can be computed by `simp` or `norm_num`.

This file is still being developed.

## Tags

integrate, integration, integrable
-/

public section


open Real Set Finset

open scoped Real Interval

variable {a b : ℝ} (n : ℕ)

namespace intervalIntegral

open MeasureTheory

variable {f : ℝ → ℝ} {μ : Measure ℝ} [IsLocallyFiniteMeasure μ] (c d : ℝ)

/-! ### Integrals of the form `c * ∫ x in a..b, f (c * x + d)` -/
section

@[simp]
theorem mul_integral_comp_mul_right : (c * ∫ x in a..b, f (x * c)) = ∫ x in a * c..b * c, f x :=
  smul_integral_comp_mul_right f c

@[simp]
theorem mul_integral_comp_mul_left : (c * ∫ x in a..b, f (c * x)) = ∫ x in c * a..c * b, f x :=
  smul_integral_comp_mul_left f c

@[simp]
theorem inv_mul_integral_comp_div : (c⁻¹ * ∫ x in a..b, f (x / c)) = ∫ x in a / c..b / c, f x :=
  inv_smul_integral_comp_div f c

@[simp]
theorem mul_integral_comp_mul_add :
    (c * ∫ x in a..b, f (c * x + d)) = ∫ x in c * a + d..c * b + d, f x :=
  smul_integral_comp_mul_add f c d

@[simp]
theorem mul_integral_comp_add_mul :
    (c * ∫ x in a..b, f (d + c * x)) = ∫ x in d + c * a..d + c * b, f x :=
  smul_integral_comp_add_mul f c d

@[simp]
theorem inv_mul_integral_comp_div_add :
    (c⁻¹ * ∫ x in a..b, f (x / c + d)) = ∫ x in a / c + d..b / c + d, f x :=
  inv_smul_integral_comp_div_add f c d

@[simp]
theorem inv_mul_integral_comp_add_div :
    (c⁻¹ * ∫ x in a..b, f (d + x / c)) = ∫ x in d + a / c..d + b / c, f x :=
  inv_smul_integral_comp_add_div f c d

@[simp]
theorem mul_integral_comp_mul_sub :
    (c * ∫ x in a..b, f (c * x - d)) = ∫ x in c * a - d..c * b - d, f x :=
  smul_integral_comp_mul_sub f c d

@[simp]
theorem mul_integral_comp_sub_mul :
    (c * ∫ x in a..b, f (d - c * x)) = ∫ x in d - c * b..d - c * a, f x :=
  smul_integral_comp_sub_mul f c d

@[simp]
theorem inv_mul_integral_comp_div_sub :
    (c⁻¹ * ∫ x in a..b, f (x / c - d)) = ∫ x in a / c - d..b / c - d, f x :=
  inv_smul_integral_comp_div_sub f c d

@[simp]
theorem inv_mul_integral_comp_sub_div :
    (c⁻¹ * ∫ x in a..b, f (d - x / c)) = ∫ x in d - b / c..d - a / c, f x :=
  inv_smul_integral_comp_sub_div f c d

end

end intervalIntegral

open intervalIntegral

/-! ### Integrals of simple functions -/


theorem integral_cpow {r : ℂ} (h : -1 < r.re ∨ r ≠ -1 ∧ (0 : ℝ) ∉ [[a, b]]) :
    (∫ x : ℝ in a..b, (x : ℂ) ^ r) = ((b : ℂ) ^ (r + 1) - (a : ℂ) ^ (r + 1)) / (r + 1) := by
  rw [sub_div]
  have hr : r + 1 ≠ 0 := by
    rcases h with h | h
    · apply_fun Complex.re
      rw [Complex.add_re, Complex.one_re, Complex.zero_re, Ne, add_eq_zero_iff_eq_neg]
      exact h.ne'
    · rw [Ne, ← add_eq_zero_iff_eq_neg] at h; exact h.1
  by_cases hab : (0 : ℝ) ∉ [[a, b]]
  · apply integral_eq_sub_of_hasDerivAt (fun x hx => ?_)
      (intervalIntegrable_cpow (r := r) <| Or.inr hab)
    refine hasDerivAt_ofReal_cpow_const' (ne_of_mem_of_not_mem hx hab) ?_
    contrapose! hr; rwa [add_eq_zero_iff_eq_neg]
  replace h : -1 < r.re := by tauto
  suffices ∀ c : ℝ, (∫ x : ℝ in 0..c, (x : ℂ) ^ r) =
      (c : ℂ) ^ (r + 1) / (r + 1) - (0 : ℂ) ^ (r + 1) / (r + 1) by
    rw [← integral_add_adjacent_intervals (@intervalIntegrable_cpow' a 0 r h)
      (@intervalIntegrable_cpow' 0 b r h), integral_symm, this a, this b, Complex.zero_cpow hr]
    ring
  intro c
  apply integral_eq_sub_of_hasDeriv_right
  · refine ((Complex.continuous_ofReal_cpow_const ?_).div_const _).continuousOn
    rwa [Complex.add_re, Complex.one_re, ← neg_lt_iff_pos_add]
  · refine fun x hx => (hasDerivAt_ofReal_cpow_const' ?_ ?_).hasDerivWithinAt
    · rcases le_total c 0 with (hc | hc)
      · rw [max_eq_left hc] at hx; exact hx.2.ne
      · rw [min_eq_left hc] at hx; exact hx.1.ne'
    · contrapose! hr; rw [hr]; ring
  · exact intervalIntegrable_cpow' h

set_option backward.isDefEq.respectTransparency false in
theorem integral_rpow {r : ℝ} (h : -1 < r ∨ r ≠ -1 ∧ (0 : ℝ) ∉ [[a, b]]) :
    ∫ x in a..b, x ^ r = (b ^ (r + 1) - a ^ (r + 1)) / (r + 1) := by
  have h' : -1 < (r : ℂ).re ∨ (r : ℂ) ≠ -1 ∧ (0 : ℝ) ∉ [[a, b]] := by
    cases h
    · left; rwa [Complex.ofReal_re]
    · right; rwa [← Complex.ofReal_one, ← Complex.ofReal_neg, Ne, Complex.ofReal_inj]
  have :
    (∫ x in a..b, (x : ℂ) ^ (r : ℂ)) = ((b : ℂ) ^ (r + 1 : ℂ) - (a : ℂ) ^ (r + 1 : ℂ)) / (r + 1) :=
    integral_cpow h'
  apply_fun Complex.re at this; convert this
  · simp_rw [intervalIntegral_eq_integral_uIoc, Complex.real_smul, Complex.re_ofReal_mul, rpow_def,
      ← RCLike.re_eq_complex_re, smul_eq_mul]
    rw [integral_re]
    refine intervalIntegrable_iff.mp ?_
    rcases h' with h' | h'
    · exact intervalIntegrable_cpow' h'
    · exact intervalIntegrable_cpow (Or.inr h'.2)
  · rw [(by push_cast; rfl : (r : ℂ) + 1 = ((r + 1 : ℝ) : ℂ))]
    simp_rw [div_eq_inv_mul, ← Complex.ofReal_inv, Complex.re_ofReal_mul, Complex.sub_re, rpow_def]

theorem integral_zpow {n : ℤ} (h : 0 ≤ n ∨ n ≠ -1 ∧ (0 : ℝ) ∉ [[a, b]]) :
    ∫ x in a..b, x ^ n = (b ^ (n + 1) - a ^ (n + 1)) / (n + 1) := by
  replace h : -1 < (n : ℝ) ∨ (n : ℝ) ≠ -1 ∧ (0 : ℝ) ∉ [[a, b]] := mod_cast h
  exact mod_cast integral_rpow h

@[simp]
theorem integral_pow : ∫ x in a..b, x ^ n = (b ^ (n + 1) - a ^ (n + 1)) / (n + 1) := by
  simpa only [← Int.natCast_succ, zpow_natCast] using integral_zpow (Or.inl n.cast_nonneg)

/-- Integral of `|x - a| ^ n` over `Ι a b`. This integral appears in the proof of the
Picard-Lindelöf/Cauchy-Lipschitz theorem. -/
theorem integral_pow_abs_sub_uIoc : ∫ x in Ι a b, |x - a| ^ n = |b - a| ^ (n + 1) / (n + 1) := by
  rcases le_or_gt a b with hab | hab
  · calc
      ∫ x in Ι a b, |x - a| ^ n = ∫ x in a..b, |x - a| ^ n := by
        rw [uIoc_of_le hab, ← integral_of_le hab]
      _ = ∫ x in 0..(b - a), x ^ n := by
        simp only [integral_comp_sub_right fun x => |x| ^ n, sub_self]
        refine integral_congr fun x hx => congr_arg₂ Pow.pow (abs_of_nonneg <| ?_) rfl
        rw [uIcc_of_le (sub_nonneg.2 hab)] at hx
        exact hx.1
      _ = |b - a| ^ (n + 1) / (n + 1) := by simp [abs_of_nonneg (sub_nonneg.2 hab)]
  · calc
      ∫ x in Ι a b, |x - a| ^ n = ∫ x in b..a, |x - a| ^ n := by
        rw [uIoc_of_ge hab.le, ← integral_of_le hab.le]
      _ = ∫ x in b - a..0, (-x) ^ n := by
        simp only [integral_comp_sub_right fun x => |x| ^ n, sub_self]
        refine integral_congr fun x hx => congr_arg₂ Pow.pow (abs_of_nonpos <| ?_) rfl
        rw [uIcc_of_le (sub_nonpos.2 hab.le)] at hx
        exact hx.2
      _ = |b - a| ^ (n + 1) / (n + 1) := by
        simp [integral_comp_neg fun x => x ^ n, abs_of_neg (sub_neg.2 hab)]

@[simp]
theorem integral_id : ∫ x in a..b, x = (b ^ 2 - a ^ 2) / 2 := by
  have := @integral_pow a b 1
  norm_num at this
  exact this

theorem integral_one : (∫ _ in a..b, (1 : ℝ)) = b - a := by
  simp only [mul_one, smul_eq_mul, integral_const]

theorem integral_const_on_unit_interval : ∫ _ in a..a + 1, b = b := by simp

@[simp]
theorem integral_inv (h : (0 : ℝ) ∉ [[a, b]]) : ∫ x in a..b, x⁻¹ = log (b / a) := by
  have h' := fun x (hx : x ∈ [[a, b]]) => ne_of_mem_of_not_mem hx h
  rw [integral_deriv_eq_sub' _ deriv_log' (fun x hx => differentiableAt_log (h' x hx))
      (continuousOn_inv₀.mono <| subset_compl_singleton_iff.mpr h),
    log_div (h' b right_mem_uIcc) (h' a left_mem_uIcc)]

@[simp]
theorem integral_inv_of_pos (ha : 0 < a) (hb : 0 < b) : ∫ x in a..b, x⁻¹ = log (b / a) :=
  integral_inv <| notMem_uIcc_of_lt ha hb

@[simp]
theorem integral_inv_of_neg (ha : a < 0) (hb : b < 0) : ∫ x in a..b, x⁻¹ = log (b / a) :=
  integral_inv <| notMem_uIcc_of_gt ha hb

theorem integral_one_div (h : (0 : ℝ) ∉ [[a, b]]) : ∫ x : ℝ in a..b, 1 / x = log (b / a) := by
  simp only [one_div, integral_inv h]

theorem integral_one_div_of_pos (ha : 0 < a) (hb : 0 < b) :
    ∫ x : ℝ in a..b, 1 / x = log (b / a) := by simp only [one_div, integral_inv_of_pos ha hb]

theorem integral_one_div_of_neg (ha : a < 0) (hb : b < 0) :
    ∫ x : ℝ in a..b, 1 / x = log (b / a) := by simp only [one_div, integral_inv_of_neg ha hb]

@[simp]
theorem integral_exp : ∫ x in a..b, exp x = exp b - exp a := by
  rw [integral_deriv_eq_sub']
  · simp
  · exact fun _ _ => differentiableAt_exp
  · exact continuousOn_exp

theorem integral_exp_mul_complex {c : ℂ} (hc : c ≠ 0) :
    (∫ x in a..b, Complex.exp (c * x)) = (Complex.exp (c * b) - Complex.exp (c * a)) / c := by
  have D : ∀ x : ℝ, HasDerivAt (fun y : ℝ => Complex.exp (c * y) / c) (Complex.exp (c * x)) x := by
    intro x
    conv => congr
    rw [← mul_div_cancel_right₀ (Complex.exp (c * x)) hc]
    apply ((Complex.hasDerivAt_exp _).comp x _).div_const c
    simpa only [mul_one] using ((hasDerivAt_id (x : ℂ)).const_mul _).comp_ofReal
  rw [integral_deriv_eq_sub' _ (funext fun x => (D x).deriv) fun x _ => (D x).differentiableAt]
  · ring
  · fun_prop

lemma integral_exp_mul_I_eq_sin (r : ℝ) :
    ∫ t in -r..r, Complex.exp (t * Complex.I) = 2 * Real.sin r :=
  calc ∫ t in -r..r, Complex.exp (t * Complex.I)
  _ = (Complex.exp (Complex.I * r) - Complex.exp (Complex.I * (-r))) / Complex.I := by
    simp_rw [mul_comm _ Complex.I]
    rw [integral_exp_mul_complex]
    · simp
    · simp
  _ = 2 * Real.sin r := by
    simp only [mul_comm Complex.I, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg,
      add_sub_add_left_eq_sub, Complex.div_I, Complex.ofReal_sin]
    rw [sub_mul, mul_assoc, mul_assoc, two_mul]
    simp

lemma integral_exp_mul_I_eq_sinc (r : ℝ) :
    ∫ t in -r..r, Complex.exp (t * Complex.I) = 2 * r * sinc r := by
  rw [integral_exp_mul_I_eq_sin]
  by_cases hr : r = 0
  · simp [hr]
  rw [sinc_of_ne_zero hr]
  norm_cast
  field

/-- Helper lemma for `integral_log`: case where `a = 0` and `b` is positive. -/
lemma integral_log_from_zero_of_pos (ht : 0 < b) : ∫ s in 0..b, log s = b * log b - b := by
  -- Compute the integral by giving a primitive and considering it limit as x approaches 0 from the
  -- right. The following lines were suggested by Gareth Ma on Zulip.
  rw [integral_eq_sub_of_hasDerivAt_of_tendsto (f := fun x ↦ x * log x - x)
    (fa := 0) (fb := b * log b - b) (hint := intervalIntegrable_log')]
  · abel
  · exact ht
  · intro s ⟨hs, _ ⟩
    simpa using (hasDerivAt_mul_log hs.ne.symm).sub (hasDerivAt_id s)
  · simpa [mul_comm] using ((tendsto_log_mul_rpow_nhdsGT_zero zero_lt_one).sub
      (tendsto_nhdsWithin_of_tendsto_nhds Filter.tendsto_id))
  · exact tendsto_nhdsWithin_of_tendsto_nhds (ContinuousAt.tendsto (by fun_prop))

/-- Helper lemma for `integral_log`: case where `a = 0`. -/
lemma integral_log_from_zero {b : ℝ} : ∫ s in 0..b, log s = b * log b - b := by
  rcases lt_trichotomy b 0 with h | h | h
  · -- If t is negative, use that log is an even function to reduce to the positive case.
    conv => arg 1; arg 1; intro t; rw [← log_neg_eq_log]
    rw [intervalIntegral.integral_comp_neg, intervalIntegral.integral_symm, neg_zero,
      integral_log_from_zero_of_pos (Left.neg_pos_iff.mpr h), log_neg_eq_log]
    ring
  · simp [h]
  · exact integral_log_from_zero_of_pos h

@[simp]
theorem integral_log : ∫ s in a..b, log s = b * log b - a * log a - b + a := by
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0)]
  · rw [intervalIntegral.integral_symm, integral_log_from_zero, integral_log_from_zero]
    ring
  all_goals exact intervalIntegrable_log'

@[simp]
theorem integral_sin : ∫ x in a..b, sin x = cos a - cos b := by
  rw [integral_deriv_eq_sub' fun x => -cos x]
  · ring
  · simp
  · simp only [differentiableAt_fun_neg_iff, differentiableAt_cos, implies_true]
  · exact continuousOn_sin

@[simp]
theorem integral_cos : ∫ x in a..b, cos x = sin b - sin a := by
  rw [integral_deriv_eq_sub']
  · simp
  · simp only [differentiableAt_sin, implies_true]
  · exact continuousOn_cos

theorem integral_cos_mul_complex {z : ℂ} (hz : z ≠ 0) (a b : ℝ) :
    (∫ x in a..b, Complex.cos (z * x)) = Complex.sin (z * b) / z - Complex.sin (z * a) / z := by
  apply integral_eq_sub_of_hasDerivAt
  swap
  · apply Continuous.intervalIntegrable <| by fun_prop
  intro x _
  have a := Complex.hasDerivAt_sin (↑x * z)
  have b : HasDerivAt (fun y => y * z : ℂ → ℂ) z ↑x := hasDerivAt_mul_const _
  have c : HasDerivAt (Complex.sin ∘ fun y : ℂ => (y * z)) _ ↑x := HasDerivAt.comp (𝕜 := ℂ) x a b
  have d := HasDerivAt.comp_ofReal (c.div_const z)
  simp only [mul_comm] at d
  convert d using 1
  conv_rhs => arg 1; rw [mul_comm]
  rw [mul_div_cancel_right₀ _ hz]

theorem integral_cos_sq_sub_sin_sq :
    ∫ x in a..b, cos x ^ 2 - sin x ^ 2 = sin b * cos b - sin a * cos a := by
  simpa only [sq, sub_eq_add_neg, neg_mul_eq_mul_neg] using
    integral_deriv_mul_eq_sub (fun x _ => hasDerivAt_sin x) (fun x _ => hasDerivAt_cos x)
      continuousOn_cos.intervalIntegrable continuousOn_sin.neg.intervalIntegrable

theorem integral_one_div_one_add_sq :
    (∫ x : ℝ in a..b, ↑1 / (↑1 + x ^ 2)) = arctan b - arctan a := by
  refine integral_deriv_eq_sub' _ Real.deriv_arctan (fun _ _ => differentiableAt_arctan _)
    (continuous_const.div ?_ fun x => ?_).continuousOn
  · fun_prop
  · nlinarith

@[simp]
theorem integral_inv_one_add_sq : (∫ x : ℝ in a..b, (↑1 + x ^ 2)⁻¹) = arctan b - arctan a := by
  simp only [← one_div, integral_one_div_one_add_sq]

@[simp]
theorem integral_inv_sq_add_sq {c : ℝ} (hc : c ≠ 0) :
    ∫ x : ℝ in a..b, (c ^ 2 + x ^ 2)⁻¹ = c⁻¹ * (arctan (b / c) - arctan (a / c)) := calc
  _ = ∫ x : ℝ in a..b, (c ^ 2)⁻¹ * (1 + (x / c) ^ 2)⁻¹ := by field_simp
  _ = _ := by
    simp [integral_comp_div (fun x => (c ^ 2)⁻¹ * (1 + x ^ 2)⁻¹) hc]
    field_simp

theorem integral_div_sq_add_sq {c : ℝ} :
    ∫ x : ℝ in a..b, c / (c ^ 2 + x ^ 2) = arctan (b / c) - arctan (a / c) := calc
  _ = ∫ x : ℝ in a..b, c * (c ^ 2 + x ^ 2)⁻¹ := by ring_nf
  _ = _ := by
    by_cases hc : c = 0
    · simp [hc]
    · rw [integral_const_mul, integral_inv_sq_add_sq hc]
      field_simp

section RpowCpow

open Complex

theorem integral_mul_cpow_one_add_sq {t : ℂ} (ht : t ≠ -1) :
    (∫ x : ℝ in a..b, (x : ℂ) * ((1 : ℂ) + ↑x ^ 2) ^ t) =
      ((1 : ℂ) + (b : ℂ) ^ 2) ^ (t + 1) / (2 * (t + ↑1)) -
      ((1 : ℂ) + (a : ℂ) ^ 2) ^ (t + 1) / (2 * (t + ↑1)) := by
  have : t + 1 ≠ 0 := by contrapose! ht; rwa [add_eq_zero_iff_eq_neg] at ht
  apply integral_eq_sub_of_hasDerivAt
  · intro x _
    have f : HasDerivAt (fun y : ℂ => 1 + y ^ 2) (2 * x : ℂ) x := by
      convert (hasDerivAt_pow 2 (x : ℂ)).const_add 1
      simp
    have g :
      ∀ {z : ℂ}, 0 < z.re → HasDerivAt (fun z => z ^ (t + 1) / (2 * (t + 1))) (z ^ t / 2) z := by
      intro z hz
      convert (HasDerivAt.cpow_const (c := t + 1) (hasDerivAt_id _)
        (Or.inl hz)).div_const (2 * (t + 1)) using 1
      simp [field]
    convert (HasDerivAt.comp (↑x) (g _) f).comp_ofReal using 1
    · ring
    · exact mod_cast add_pos_of_pos_of_nonneg zero_lt_one (sq_nonneg x)
  · apply Continuous.intervalIntegrable
    refine continuous_ofReal.mul ?_
    apply Continuous.cpow (by fun_prop) continuous_const
    intro a
    norm_cast
    exact ofReal_mem_slitPlane.2 <| add_pos_of_pos_of_nonneg one_pos <| sq_nonneg a

theorem integral_mul_rpow_one_add_sq {t : ℝ} (ht : t ≠ -1) :
    (∫ x : ℝ in a..b, x * (↑1 + x ^ 2) ^ t) =
      (↑1 + b ^ 2) ^ (t + 1) / (↑2 * (t + ↑1)) - (↑1 + a ^ 2) ^ (t + 1) / (↑2 * (t + ↑1)) := by
  have : ∀ x s : ℝ, (((↑1 + x ^ 2) ^ s : ℝ) : ℂ) = (1 + (x : ℂ) ^ 2) ^ (s : ℂ) := by
    intro x s
    norm_cast
    rw [ofReal_cpow, ofReal_add, ofReal_pow, ofReal_one]
    exact add_nonneg zero_le_one (sq_nonneg x)
  rw [← ofReal_inj]
  convert integral_mul_cpow_one_add_sq (_ : (t : ℂ) ≠ -1)
  · rw [← intervalIntegral.integral_ofReal]
    congr with x : 1
    rw [ofReal_mul, this x t]
  · simp_rw [ofReal_sub, ofReal_div, this a (t + 1), this b (t + 1)]
    push_cast; rfl
  · rw [← ofReal_one, ← ofReal_neg, Ne, ofReal_inj]
    exact ht

end RpowCpow

open Nat

/-! ### Integral of `sin x ^ n` -/

theorem integral_sin_pow_aux :
    (∫ x in a..b, sin x ^ (n + 2)) =
      (sin a ^ (n + 1) * cos a - sin b ^ (n + 1) * cos b + (↑n + 1) * ∫ x in a..b, sin x ^ n) -
        (↑n + 1) * ∫ x in a..b, sin x ^ (n + 2) := by
  let C := sin a ^ (n + 1) * cos a - sin b ^ (n + 1) * cos b
  have h : ∀ α β γ : ℝ, β * α * γ * α = β * (α * α * γ) := fun α β γ => by ring
  have hu : ∀ x ∈ [[a, b]],
      HasDerivAt (fun y => sin y ^ (n + 1)) ((n + 1 : ℕ) * cos x * sin x ^ n) x :=
    fun x _ => by simpa only [mul_right_comm] using (hasDerivAt_sin x).pow (n + 1)
  have hv : ∀ x ∈ [[a, b]], HasDerivAt (-cos) (sin x) x := fun x _ => by
    simpa only [neg_neg] using (hasDerivAt_cos x).neg
  have H := integral_mul_deriv_eq_deriv_mul hu hv ?_ ?_
  · calc
      (∫ x in a..b, sin x ^ (n + 2)) = ∫ x in a..b, sin x ^ (n + 1) * sin x := by
        simp only [_root_.pow_succ]
      _ = C + (↑n + 1) * ∫ x in a..b, cos x ^ 2 * sin x ^ n := by simp [H, h, sq]; ring
      _ = C + (↑n + 1) * ∫ x in a..b, sin x ^ n - sin x ^ (n + 2) := by
        simp [cos_sq', sub_mul, ← pow_add, add_comm]
      _ = (C + (↑n + 1) * ∫ x in a..b, sin x ^ n) - (↑n + 1) * ∫ x in a..b, sin x ^ (n + 2) := by
        rw [integral_sub, mul_sub, add_sub_assoc] <;>
          apply Continuous.intervalIntegrable <;> fun_prop
  all_goals apply Continuous.intervalIntegrable; fun_prop

/-- The reduction formula for the integral of `sin x ^ n` for any natural `n ≥ 2`. -/
theorem integral_sin_pow :
    (∫ x in a..b, sin x ^ (n + 2)) =
      (sin a ^ (n + 1) * cos a - sin b ^ (n + 1) * cos b) / (n + 2) +
        (n + 1) / (n + 2) * ∫ x in a..b, sin x ^ n := by
  field_simp
  convert eq_sub_iff_add_eq.mp (integral_sin_pow_aux n) using 1
  ring

@[simp]
theorem integral_sin_sq : ∫ x in a..b, sin x ^ 2 = (sin a * cos a - sin b * cos b + b - a) / 2 := by
  simp [field, integral_sin_pow, add_sub_assoc]

theorem integral_sin_pow_odd :
    (∫ x in 0..π, sin x ^ (2 * n + 1)) = 2 * ∏ i ∈ range n, (2 * (i : ℝ) + 2) / (2 * i + 3) := by
  induction n with
  | zero => norm_num
  | succ k ih =>
    rw [prod_range_succ_comm, mul_left_comm, ← ih, mul_succ, integral_sin_pow]
    norm_cast
    field_simp
    simp

theorem integral_sin_pow_even :
    (∫ x in 0..π, sin x ^ (2 * n)) = π * ∏ i ∈ range n, (2 * (i : ℝ) + 1) / (2 * i + 2) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [prod_range_succ_comm, mul_left_comm, ← ih, mul_succ, integral_sin_pow]
    norm_cast
    field_simp
    simp

theorem integral_sin_pow_pos : 0 < ∫ x in 0..π, sin x ^ n := by
  rcases even_or_odd' n with ⟨k, rfl | rfl⟩ <;>
  simp only [integral_sin_pow_even, integral_sin_pow_odd] <;>
  refine mul_pos (by simp [pi_pos]) (prod_pos fun n _ => div_pos ?_ ?_) <;>
  norm_cast <;>
  lia

theorem integral_sin_pow_succ_le : (∫ x in 0..π, sin x ^ (n + 1)) ≤ ∫ x in 0..π, sin x ^ n := by
  let H x h := pow_le_pow_of_le_one (sin_nonneg_of_mem_Icc h) (sin_le_one x) (n.le_add_right 1)
  refine integral_mono_on pi_pos.le ?_ ?_ H <;> exact (continuous_sin.pow _).intervalIntegrable 0 π

theorem integral_sin_pow_antitone : Antitone fun n : ℕ => ∫ x in 0..π, sin x ^ n :=
  antitone_nat_of_succ_le integral_sin_pow_succ_le

/-! ### Integral of `cos x ^ n` -/


theorem integral_cos_pow_aux :
    (∫ x in a..b, cos x ^ (n + 2)) =
      (cos b ^ (n + 1) * sin b - cos a ^ (n + 1) * sin a + (n + 1) * ∫ x in a..b, cos x ^ n) -
        (n + 1) * ∫ x in a..b, cos x ^ (n + 2) := by
  let C := cos b ^ (n + 1) * sin b - cos a ^ (n + 1) * sin a
  have h : ∀ α β γ : ℝ, β * α * γ * α = β * (α * α * γ) := fun α β γ => by ring
  have hu : ∀ x ∈ [[a, b]],
      HasDerivAt (fun y => cos y ^ (n + 1)) (-(n + 1 : ℕ) * sin x * cos x ^ n) x :=
    fun x _ => by
      simpa only [mul_right_comm, neg_mul, mul_neg] using (hasDerivAt_cos x).pow (n + 1)
  have hv : ∀ x ∈ [[a, b]], HasDerivAt sin (cos x) x := fun x _ => hasDerivAt_sin x
  have H := integral_mul_deriv_eq_deriv_mul hu hv ?_ ?_
  · calc
      (∫ x in a..b, cos x ^ (n + 2)) = ∫ x in a..b, cos x ^ (n + 1) * cos x := by
        simp only [_root_.pow_succ]
      _ = C + (n + 1) * ∫ x in a..b, sin x ^ 2 * cos x ^ n := by simp [C, H, h, sq, -neg_add_rev]
      _ = C + (n + 1) * ∫ x in a..b, cos x ^ n - cos x ^ (n + 2) := by
        simp [sin_sq, sub_mul, ← pow_add, add_comm]
      _ = (C + (n + 1) * ∫ x in a..b, cos x ^ n) - (n + 1) * ∫ x in a..b, cos x ^ (n + 2) := by
        rw [integral_sub, mul_sub, add_sub_assoc] <;>
          apply Continuous.intervalIntegrable <;> fun_prop
  all_goals apply Continuous.intervalIntegrable; fun_prop

/-- The reduction formula for the integral of `cos x ^ n` for any natural `n ≥ 2`. -/
theorem integral_cos_pow :
    (∫ x in a..b, cos x ^ (n + 2)) =
      (cos b ^ (n + 1) * sin b - cos a ^ (n + 1) * sin a) / (n + 2) +
        (n + 1) / (n + 2) * ∫ x in a..b, cos x ^ n := by
  field_simp
  convert eq_sub_iff_add_eq.mp (integral_cos_pow_aux n) using 1
  ring

@[simp]
theorem integral_cos_sq : ∫ x in a..b, cos x ^ 2 = (cos b * sin b - cos a * sin a + b - a) / 2 := by
  simp [field, integral_cos_pow, add_sub_assoc]

/-! ### Integral of `sin x ^ m * cos x ^ n` -/


/-- Simplification of the integral of `sin x ^ m * cos x ^ n`, case `n` is odd. -/
theorem integral_sin_pow_mul_cos_pow_odd (m n : ℕ) :
    (∫ x in a..b, sin x ^ m * cos x ^ (2 * n + 1)) = ∫ u in sin a..sin b, u ^ m * (1 - u ^ 2) ^ n :=
  have hc : Continuous fun u : ℝ => u ^ m * (↑1 - u ^ 2) ^ n := by fun_prop
  calc
    (∫ x in a..b, sin x ^ m * cos x ^ (2 * n + 1)) =
        ∫ x in a..b, sin x ^ m * (↑1 - sin x ^ 2) ^ n * cos x := by
      simp only [_root_.pow_zero, _root_.pow_succ, mul_assoc, pow_mul, one_mul]
      congr! 5
      rw [← sq, ← sq, cos_sq']
    _ = ∫ u in sin a..sin b, u ^ m * (1 - u ^ 2) ^ n :=
      integral_comp_mul_deriv (fun x _ => hasDerivAt_sin x) continuousOn_cos hc

/-- The integral of `sin x * cos x`, given in terms of sin².
  See `integral_sin_mul_cos₂` below for the integral given in terms of cos². -/
@[simp]
theorem integral_sin_mul_cos₁ : ∫ x in a..b, sin x * cos x = (sin b ^ 2 - sin a ^ 2) / 2 := by
  simpa using integral_sin_pow_mul_cos_pow_odd 1 0

@[simp]
theorem integral_sin_sq_mul_cos :
    ∫ x in a..b, sin x ^ 2 * cos x = (sin b ^ 3 - sin a ^ 3) / 3 := by
  have := @integral_sin_pow_mul_cos_pow_odd a b 2 0
  norm_num at this; exact this

@[simp]
theorem integral_cos_pow_three :
    ∫ x in a..b, cos x ^ 3 = sin b - sin a - (sin b ^ 3 - sin a ^ 3) / 3 := by
  have := @integral_sin_pow_mul_cos_pow_odd a b 0 1
  norm_num at this; exact this

/-- Simplification of the integral of `sin x ^ m * cos x ^ n`, case `m` is odd. -/
theorem integral_sin_pow_odd_mul_cos_pow (m n : ℕ) :
    (∫ x in a..b, sin x ^ (2 * m + 1) * cos x ^ n) = ∫ u in cos b..cos a, u ^ n * (1 - u ^ 2) ^ m :=
  have hc : Continuous fun u : ℝ => u ^ n * (↑1 - u ^ 2) ^ m := by fun_prop
  calc
    (∫ x in a..b, sin x ^ (2 * m + 1) * cos x ^ n) =
        -∫ x in b..a, sin x ^ (2 * m + 1) * cos x ^ n := by rw [integral_symm]
    _ = ∫ x in b..a, (↑1 - cos x ^ 2) ^ m * -sin x * cos x ^ n := by
      simp only [_root_.pow_succ, pow_mul, _root_.pow_zero, one_mul, mul_neg, neg_mul,
        integral_neg, neg_inj]
      congr! 5
      rw [← sq, ← sq, sin_sq]
    _ = ∫ x in b..a, cos x ^ n * (↑1 - cos x ^ 2) ^ m * -sin x := by congr; ext; ring
    _ = ∫ u in cos b..cos a, u ^ n * (↑1 - u ^ 2) ^ m :=
      integral_comp_mul_deriv (fun x _ => hasDerivAt_cos x) continuousOn_sin.neg hc

/-- The integral of `sin x * cos x`, given in terms of cos².
See `integral_sin_mul_cos₁` above for the integral given in terms of sin². -/
theorem integral_sin_mul_cos₂ : ∫ x in a..b, sin x * cos x = (cos a ^ 2 - cos b ^ 2) / 2 := by
  simpa using integral_sin_pow_odd_mul_cos_pow 0 1

@[simp]
theorem integral_sin_mul_cos_sq :
    ∫ x in a..b, sin x * cos x ^ 2 = (cos a ^ 3 - cos b ^ 3) / 3 := by
  have := @integral_sin_pow_odd_mul_cos_pow a b 0 2
  norm_num at this; exact this

@[simp]
theorem integral_sin_pow_three :
    ∫ x in a..b, sin x ^ 3 = cos a - cos b - (cos a ^ 3 - cos b ^ 3) / 3 := by
  have := @integral_sin_pow_odd_mul_cos_pow a b 1 0
  norm_num at this; exact this

/-- Simplification of the integral of `sin x ^ m * cos x ^ n`, case `m` and `n` are both even. -/
theorem integral_sin_pow_even_mul_cos_pow_even (m n : ℕ) :
    (∫ x in a..b, sin x ^ (2 * m) * cos x ^ (2 * n)) =
      ∫ x in a..b, ((1 - cos (2 * x)) / 2) ^ m * ((1 + cos (2 * x)) / 2) ^ n := by
  simp [pow_mul, sin_sq, cos_sq, ← sub_sub]
  field_simp
  norm_num

@[simp]
theorem integral_sin_sq_mul_cos_sq :
    ∫ x in a..b, sin x ^ 2 * cos x ^ 2 = (b - a) / 8 - (sin (4 * b) - sin (4 * a)) / 32 := by
  convert integral_sin_pow_even_mul_cos_pow_even 1 1 using 1
  have h1 : ∀ c : ℝ, (↑1 - c) / ↑2 * ((↑1 + c) / ↑2) = (↑1 - c ^ 2) / 4 := fun c => by ring
  have h2 : Continuous fun x => cos (2 * x) ^ 2 := by fun_prop
  have h3 : ∀ x, cos x * sin x = sin (2 * x) / 2 := by intro; rw [sin_two_mul]; ring
  have h4 : ∀ d : ℝ, 2 * (2 * d) = 4 * d := fun d => by ring
  simp [h1, h2.intervalIntegrable, integral_comp_mul_left fun x => cos x ^ 2, h3, h4]
  ring

/-! ### Integral of miscellaneous functions -/

theorem integral_sqrt_one_sub_sq : ∫ x in (-1 : ℝ)..1, √(1 - x ^ 2 : ℝ) = π / 2 :=
  calc
    _ = ∫ x in sin (-(π / 2))..sin (π / 2), √(1 - x ^ 2 : ℝ) := by rw [sin_neg, sin_pi_div_two]
    _ = ∫ x in (-(π / 2))..(π / 2), √(1 - sin x ^ 2 : ℝ) * cos x :=
          (integral_comp_mul_deriv (fun x _ => hasDerivAt_sin x) continuousOn_cos
            (by fun_prop)).symm
    _ = ∫ x in (-(π / 2))..(π / 2), cos x ^ 2 := by
          refine integral_congr_ae (MeasureTheory.ae_of_all _ fun _ h => ?_)
          rw [uIoc_of_le (neg_le_self (le_of_lt (half_pos Real.pi_pos))), Set.mem_Ioc] at h
          rw [← Real.cos_eq_sqrt_one_sub_sin_sq (le_of_lt h.1) h.2, pow_two]
    _ = π / 2 := by simp
