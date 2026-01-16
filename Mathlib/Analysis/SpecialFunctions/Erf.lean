/-
Copyright (c) 2025 The Mathlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Oudard
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Error Function

This file defines the error function `erf` and the complementary error function `erfc`,
and proves their basic properties.

## Main definitions

* `Real.erf`: The error function, defined as `(2/√π) ∫₀ˣ e^(-t²) dt`
* `Real.erfc`: The complementary error function, defined as `1 - erf x`
* `Complex.erf`: The complex error function, defined as the line integral from 0 to z

## Main results

* `Real.erf_zero`: `erf 0 = 0`
* `Real.erf_neg`: `erf` is an odd function: `erf (-x) = -erf x`
* `Real.erf_tendsto_one`: `erf x → 1` as `x → ∞`
* `Real.erf_tendsto_neg_one`: `erf x → -1` as `x → -∞`
* `Real.erf_le_one`: `erf x ≤ 1` for all `x`
* `Real.neg_one_le_erf`: `-1 ≤ erf x` for all `x`
* `Real.deriv_erf`: `deriv erf x = (2/√π) * exp(-x²)`
* `Real.differentiable_erf`: `erf` is differentiable
* `Real.continuous_erf`: `erf` is continuous
* `Real.strictMono_erf`: `erf` is strictly monotone
* `Complex.erf_ofReal`: `Complex.erf x = Real.erf x` for real `x`
* `Complex.erf_neg`: `erf` is an odd function: `erf (-z) = -erf z`

## References

* <https://en.wikipedia.org/wiki/Error_function>
-/

open MeasureTheory Set Filter Topology

public noncomputable section

namespace Real

/-! ### Error Function -/

/-- The error function `erf(x) = (2/√π) ∫₀ˣ e^(-t²) dt`. -/
def erf (x : ℝ) : ℝ :=
  (2 / sqrt π) * ∫ t in (0)..x, exp (-(t ^ 2))

/-- The complementary error function `erfc(x) = 1 - erf(x)`. -/
def erfc (x : ℝ) : ℝ := 1 - erf x

@[simp]
theorem erf_zero : erf 0 = 0 := by
  simp only [erf, intervalIntegral.integral_same, mul_zero]

@[simp]
theorem erfc_zero : erfc 0 = 1 := by
  simp only [erfc, erf_zero, sub_zero]

/-- `e^(-t²)` is an even function. -/
theorem exp_neg_sq_even (t : ℝ) : exp (-((-t) ^ 2)) = exp (-(t ^ 2)) := by
  ring_nf

/-- `erf` is an odd function: `erf(-x) = -erf(x)`. -/
theorem erf_neg (x : ℝ) : erf (-x) = -erf x := by
  simp only [erf]
  have h : ∫ t in (0 : ℝ)..-x, exp (-(t ^ 2)) = -∫ t in (0 : ℝ)..x, exp (-(t ^ 2)) := by
    rw [intervalIntegral.integral_symm]
    have hsub : ∫ t in (-x : ℝ)..0, exp (-(t ^ 2)) = ∫ t in (0 : ℝ)..x, exp (-(t ^ 2)) := by
      let f : ℝ → ℝ := fun t => exp (-(t ^ 2))
      have hcomp : (-1 : ℝ) * ∫ t in (0 : ℝ)..x, f (t * (-1)) =
          ∫ t in (0 * (-1) : ℝ)..x * (-1), f t :=
        intervalIntegral.mul_integral_comp_mul_right (-1)
      simp only [mul_neg, mul_one, neg_zero] at hcomp
      have heven : (fun t => f (-t)) = f := by
        ext t
        change exp (-((-t) ^ 2)) = exp (-(t ^ 2))
        ring_nf
      rw [heven] at hcomp
      have hsym := intervalIntegral.integral_symm (f := f) (μ := volume) (a := 0) (b := -x)
      simp only [f] at hcomp hsym ⊢
      linarith
    rw [hsub]
  rw [h]
  ring

/-- `erfc` satisfies `erfc(-x) = 2 - erfc(x)`. -/
theorem erfc_neg (x : ℝ) : erfc (-x) = 2 - erfc x := by
  simp only [erfc, erf_neg]
  ring

/-- The half-line Gaussian integral: `∫_0^∞ e^(-t²) dt = √π/2`. -/
theorem integral_exp_neg_sq_Ioi : ∫ t in Ioi (0 : ℝ), exp (-(t ^ 2)) = sqrt π / 2 := by
  have h := integral_gaussian_Ioi (1 : ℝ)
  simp only [div_one] at h
  convert h using 2
  funext x
  ring_nf

/-- `erf` is non-negative for non-negative arguments. -/
theorem erf_nonneg_of_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ erf x := by
  simp only [erf]
  apply mul_nonneg
  · apply div_nonneg <;> positivity
  · apply intervalIntegral.integral_nonneg hx
    intro t _
    exact exp_nonneg _

/-- `erfc` is at most 1 for non-negative arguments. -/
theorem erfc_le_one_of_nonneg {x : ℝ} (hx : 0 ≤ x) : erfc x ≤ 1 := by
  simp only [erfc]
  linarith [erf_nonneg_of_nonneg hx]

/-- `erf(∞) = 1` (limit as `x → ∞`). -/
theorem erf_tendsto_one : Tendsto erf atTop (𝓝 1) := by
  unfold erf
  have hinteg : IntegrableOn (fun t => exp (-(t ^ 2))) (Ioi 0) := by
    have heq : (fun t => exp (-(t ^ 2))) = (fun t => exp (-1 * t ^ 2)) := by
      funext t; ring_nf
    rw [heq]
    exact (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)).integrableOn
  have hlim := intervalIntegral_tendsto_integral_Ioi (f := fun t => exp (-(t ^ 2)))
    (a := 0) hinteg tendsto_id
  have hgoal : ∫ t in Ioi (0 : ℝ), exp (-(t ^ 2)) = sqrt π / 2 := integral_exp_neg_sq_Ioi
  rw [hgoal] at hlim
  have hpos : sqrt π ≠ 0 := ne_of_gt (sqrt_pos.mpr pi_pos)
  have heq : (2 / sqrt π) * (sqrt π / 2) = 1 := by field_simp
  have hcont : Continuous (fun y => (2 / sqrt π) * y) := by continuity
  have hmul := hcont.tendsto (sqrt π / 2)
  simp only [heq] at hmul
  exact hmul.comp hlim

/-- `erfc(∞) = 0` (limit as `x → ∞`). -/
theorem erfc_tendsto_zero : Tendsto erfc atTop (𝓝 0) := by
  have h : erfc = fun x => 1 - erf x := rfl
  rw [h]
  have herf := erf_tendsto_one
  convert herf.const_sub 1
  ring

/-- `erf(-∞) = -1` (limit as `x → -∞`). -/
theorem erf_tendsto_neg_one : Tendsto erf atBot (𝓝 (-1)) := by
  have h : erf = fun x => -erf (-x) := by funext x; rw [erf_neg]; ring
  rw [h]
  have hneg : Tendsto (fun x : ℝ => -x) atBot atTop := tendsto_neg_atBot_atTop
  have h1 : Tendsto erf atTop (𝓝 1) := erf_tendsto_one
  have h2 : Tendsto (fun x => -erf (-x)) atBot (𝓝 (-1)) := by
    have hcomp : Tendsto (fun x => erf (-x)) atBot (𝓝 1) := h1.comp hneg
    exact hcomp.neg
  exact h2

/-- `erfc(-∞) = 2` (limit as `x → -∞`). -/
theorem erfc_tendsto_two : Tendsto erfc atBot (𝓝 2) := by
  have h : erfc = fun x => 1 - erf x := rfl
  rw [h]
  have herf := erf_tendsto_neg_one
  have := herf.const_sub 1
  simp only [sub_neg_eq_add] at this
  convert this using 1
  norm_num

/-- `erf x ≤ 1` for all `x`. -/
theorem erf_le_one (x : ℝ) : erf x ≤ 1 := by
  by_cases hx : 0 ≤ x
  · simp only [erf]
    have hint : ∫ t in (0 : ℝ)..x, exp (-(t ^ 2)) ≤ sqrt π / 2 := by
      calc ∫ t in (0 : ℝ)..x, exp (-(t ^ 2))
          = ∫ t in Ioc 0 x, exp (-(t ^ 2)) := by
            rw [intervalIntegral.integral_of_le hx]
        _ ≤ ∫ t in Ioi (0 : ℝ), exp (-(t ^ 2)) := by
            apply setIntegral_mono_set
            · have hinteg : Integrable (fun x => exp (-1 * x ^ 2)) :=
                integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)
              have heq : (fun x => exp (-(x ^ 2))) = (fun x => exp (-1 * x ^ 2)) := by
                funext t; ring_nf
              rw [heq]
              exact hinteg.integrableOn
            · filter_upwards with t
              exact exp_nonneg _
            · exact Ioc_subset_Ioi_self.eventuallyLE
        _ = sqrt π / 2 := integral_exp_neg_sq_Ioi
    have hpos : 0 < sqrt π := sqrt_pos.mpr pi_pos
    calc (2 / sqrt π) * ∫ t in (0 : ℝ)..x, exp (-(t ^ 2))
        ≤ (2 / sqrt π) * (sqrt π / 2) := by
          apply mul_le_mul_of_nonneg_left hint
          positivity
      _ = 1 := by field_simp
  · push_neg at hx
    have h : erf x = -erf (-x) := by rw [erf_neg]; ring
    rw [h]
    have hpos : 0 ≤ erf (-x) := erf_nonneg_of_nonneg (le_of_lt (neg_pos.mpr hx))
    linarith

/-- `-1 ≤ erf x` for all `x`. -/
theorem neg_one_le_erf (x : ℝ) : -1 ≤ erf x := by
  by_cases hx : 0 ≤ x
  · have h := erf_nonneg_of_nonneg hx
    linarith
  · push_neg at hx
    have h : erf x = -erf (-x) := by rw [erf_neg]; ring
    rw [h]
    have hle : erf (-x) ≤ 1 := erf_le_one (-x)
    linarith

/-- `0 ≤ erfc x` for all `x`. -/
theorem erfc_nonneg (x : ℝ) : 0 ≤ erfc x := by
  simp only [erfc]
  linarith [erf_le_one x]

/-- `erfc x ≤ 2` for all `x`. -/
theorem erfc_le_two (x : ℝ) : erfc x ≤ 2 := by
  simp only [erfc]
  linarith [neg_one_le_erf x]

/-- Derivative of `erf`: `erf'(x) = (2/√π) e^(-x²)`. -/
theorem hasDerivAt_erf (x : ℝ) : HasDerivAt erf ((2 / sqrt π) * exp (-(x ^ 2))) x := by
  unfold erf
  have hcont : Continuous (fun t => exp (-(t ^ 2))) := by continuity
  have hftc := hcont.integral_hasStrictDerivAt 0 x
  exact hftc.hasDerivAt.const_mul (2 / sqrt π)

theorem deriv_erf (x : ℝ) : deriv erf x = (2 / sqrt π) * exp (-(x ^ 2)) :=
  (hasDerivAt_erf x).deriv

/-- `erf` is differentiable. -/
theorem differentiable_erf : Differentiable ℝ erf := fun x => (hasDerivAt_erf x).differentiableAt

/-- `erf` is continuous. -/
theorem continuous_erf : Continuous erf := differentiable_erf.continuous

/-- `erfc` is differentiable. -/
theorem differentiable_erfc : Differentiable ℝ erfc := by
  unfold erfc
  exact (differentiable_const 1).sub differentiable_erf

/-- `erfc` is continuous. -/
theorem continuous_erfc : Continuous erfc := differentiable_erfc.continuous

/-- Derivative of `erfc`: `erfc'(x) = -(2/√π) e^(-x²)`. -/
theorem hasDerivAt_erfc (x : ℝ) : HasDerivAt erfc (-(2 / sqrt π) * exp (-(x ^ 2))) x := by
  unfold erfc
  have h := hasDerivAt_erf x
  have h1 := (hasDerivAt_const x 1).sub h
  convert h1 using 1
  ring

theorem deriv_erfc (x : ℝ) : deriv erfc x = -(2 / sqrt π) * exp (-(x ^ 2)) :=
  (hasDerivAt_erfc x).deriv

/-- `erf` is strictly monotone (since its derivative is always positive). -/
theorem strictMono_erf : StrictMono erf := by
  apply strictMono_of_deriv_pos
  intro x
  rw [deriv_erf]
  apply mul_pos
  · apply div_pos (by norm_num : (0 : ℝ) < 2) (sqrt_pos.mpr pi_pos)
  · exact exp_pos _

/-- `erfc` is strictly antitone. -/
theorem strictAnti_erfc : StrictAnti erfc := fun _ _ h => by
  simp only [erfc]
  linarith [strictMono_erf h]

/-- `erf` is monotone. -/
theorem monotone_erf : Monotone erf := strictMono_erf.monotone

/-- `erfc` is antitone. -/
theorem antitone_erfc : Antitone erfc := strictAnti_erfc.antitone

end Real

/-! ### Complex Error Function -/

namespace Complex

/-- The complex error function, defined as `erf(z) = (2/√π) · z · ∫₀¹ e^(-(tz)²) dt`.
This is the integral of `(2/√π) e^(-w²)` along the straight line from 0 to z,
using the parametrization `w = tz` for `t ∈ [0,1]`. -/
def erf (z : ℂ) : ℂ :=
  (2 / Real.sqrt Real.pi) * z * ∫ t in (0 : ℝ)..1, exp (-(t * z) ^ 2)

@[simp]
theorem erf_zero : erf 0 = 0 := by simp [erf]

/-- The complex `erf` agrees with the real `erf` on real inputs. -/
theorem erf_ofReal (x : ℝ) : erf x = Real.erf x := by
  simp only [erf, Real.erf]
  by_cases hx : x = 0
  · simp [hx]
  · -- Use change of variables: u = t * x, so ∫₀ˣ e^(-u²) du = x * ∫₀¹ e^(-(tx)²) dt
    -- First establish the real change of variables
    have hcov : ∫ u in (0 : ℝ)..x, Real.exp (-(u ^ 2)) =
        x * ∫ t in (0 : ℝ)..1, Real.exp (-((t * x) ^ 2)) := by
      have h := intervalIntegral.integral_comp_mul_right
        (f := fun u => Real.exp (-(u ^ 2))) (c := x) (a := 0) (b := 1)
      simp only [zero_mul, one_mul] at h
      have heq := h hx
      rw [smul_eq_mul] at heq
      -- heq : ∫ t in 0..1, exp(-(t*x)²) = x⁻¹ * ∫ u in 0..x, exp(-u²)
      calc ∫ u in (0 : ℝ)..x, Real.exp (-(u ^ 2))
          = x * x⁻¹ * ∫ u in (0 : ℝ)..x, Real.exp (-(u ^ 2)) := by field_simp
        _ = x * ∫ t in (0 : ℝ)..1, Real.exp (-((t * x) ^ 2)) := by rw [mul_assoc, ← heq]
    -- Now show complex integral equals real integral (for real inputs)
    have hinteg : ∫ t in (0 : ℝ)..1, exp (-((t : ℂ) * x) ^ 2) =
        ↑(∫ t in (0 : ℝ)..1, Real.exp (-((t * x) ^ 2))) := by
      rw [← intervalIntegral.integral_ofReal]
      apply intervalIntegral.integral_congr
      intro t _
      simp only [ofReal_exp, ofReal_neg, ofReal_pow, ofReal_mul]
    rw [hcov, hinteg]
    simp only [ofReal_mul, ofReal_div, ofReal_ofNat]
    ring

/-- `erf` is an odd function: `erf(-z) = -erf(z)`. -/
theorem erf_neg (z : ℂ) : erf (-z) = -erf z := by
  simp only [erf]
  have h : ∫ t in (0 : ℝ)..1, exp (-((t : ℂ) * -z) ^ 2) =
      ∫ t in (0 : ℝ)..1, exp (-((t : ℂ) * z) ^ 2) := by
    apply intervalIntegral.integral_congr
    intro t _
    simp only [mul_neg, neg_sq]
  rw [h]
  simp only [mul_neg, neg_mul]

end Complex
