/-
Copyright (c) 2022 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Analysis.MellinTransform
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Derivative of the Gamma function

This file shows that the (complex) `Γ` function is complex-differentiable at all `s : ℂ` with
`s ∉ {-n : n ∈ ℕ}`, as well as the real counterpart.

## Main results

* `Complex.differentiableAt_Gamma`: `Γ` is complex-differentiable at all `s : ℂ` with
  `s ∉ {-n : n ∈ ℕ}`.
* `Real.differentiableAt_Gamma`: `Γ` is real-differentiable at all `s : ℝ` with
  `s ∉ {-n : n ∈ ℕ}`.

## Tags

Gamma
-/

public section


noncomputable section

open Filter Set Real Asymptotics
open scoped Topology

namespace Complex

/-! Now check that the `Γ` function is differentiable, wherever this makes sense. -/


section GammaHasDeriv

/-- Rewrite the Gamma integral as an example of a Mellin transform. -/
theorem GammaIntegral_eq_mellin : GammaIntegral = mellin fun x => ↑(Real.exp (-x)) :=
  funext fun s => by simp only [mellin, GammaIntegral, smul_eq_mul, mul_comm]

/-- The derivative of the `Γ` integral, at any `s ∈ ℂ` with `1 < re s`, is given by the Mellin
transform of `log t * exp (-t)`. -/
theorem hasDerivAt_GammaIntegral {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt GammaIntegral (∫ t : ℝ in Ioi 0, t ^ (s - 1) * (Real.log t * Real.exp (-t))) s := by
  rw [GammaIntegral_eq_mellin]
  convert! (mellin_hasDerivAt_of_isBigO_rpow (E := ℂ) _ _ (lt_add_one _) _ hs).2
  · refine (Continuous.continuousOn ?_).locallyIntegrableOn measurableSet_Ioi
    exact continuous_ofReal.comp (Real.continuous_exp.comp continuous_neg)
  · rw [← isBigO_norm_left]
    simp_rw [norm_real, isBigO_norm_left]
    simpa only [neg_one_mul] using (isLittleO_exp_neg_mul_rpow_atTop zero_lt_one _).isBigO
  · simp_rw [neg_zero, rpow_zero]
    refine isBigO_const_of_tendsto (?_ : Tendsto _ _ (𝓝 (1 : ℂ))) one_ne_zero
    rw [(by simp : (1 : ℂ) = Real.exp (-0))]
    exact (continuous_ofReal.comp (Real.continuous_exp.comp continuous_neg)).continuousWithinAt

theorem hasDerivAt_Gamma {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt Gamma (∫ t : ℝ in Ioi 0, t ^ (s - 1) * (Real.log t * Real.exp (-t))) s := by
  have : IsOpen {s : ℂ | 0 < s.re} := continuous_re.isOpen_preimage _ isOpen_Ioi
  apply (hasDerivAt_GammaIntegral (by simpa using hs)).congr_of_eventuallyEq
  filter_upwards [this.mem_nhds hs] with a using Gamma_eq_integral

@[fun_prop]
theorem differentiableAt_Gamma (s : ℂ) (hs : ∀ m : ℕ, s ≠ -m) : DifferentiableAt ℂ Gamma s := by
  -- We will show, by induction on `n`, that `Gamma` is differentiable on `-n < Re s`.
  suffices ∀ (n : ℕ) (s : ℂ) (hsre : -n < s.re) (hs : ∀ m : ℕ, s ≠ -m), DifferentiableAt ℂ _ s from
    this (⌊-s.re⌋₊ + 1) s (by grind [Nat.lt_floor_add_one (-s.re)]) hs
  intro n s hsre hs
  induction n generalizing s with
  | zero => exact (hasDerivAt_Gamma (by simpa using hsre)).differentiableAt
  | succ n IH =>
    -- Induction step: use recurrence relation
    have hsne : s ≠ 0 := by grind [hs 0]
    specialize IH (s + 1) (by grind [add_re, one_re]) (fun m ↦ by grind [hs (m + 1)])
    have := IH.comp s (show DifferentiableAt ℂ (fun s ↦ s + 1) s by fun_prop)
    apply (this.fun_div differentiableAt_id hsne).congr_of_eventuallyEq
    filter_upwards [isOpen_ne.mem_nhds hsne] using by grind [Gamma_add_one]

theorem differentiableAt_Gamma_one : DifferentiableAt ℂ Gamma 1 :=
  differentiableAt_Gamma 1 (by norm_cast; simp)

theorem continuousAt_Gamma (s : ℂ) (hs : ∀ m : ℕ, s ≠ -m) : ContinuousAt Gamma s :=
  (differentiableAt_Gamma s hs).continuousAt

theorem continuousAt_Gamma_one : ContinuousAt Gamma 1 :=
  differentiableAt_Gamma_one.continuousAt

/-- At `s = 0`, the Gamma function has a simple pole with residue 1. -/
theorem tendsto_self_mul_Gamma_nhds_zero : Tendsto (fun z : ℂ => z * Gamma z) (𝓝[≠] 0) (𝓝 1) := by
  rw [show 𝓝 (1 : ℂ) = 𝓝 (Gamma (0 + 1)) by simp only [zero_add, Complex.Gamma_one]]
  refine tendsto_nhdsWithin_congr Gamma_add_one (continuousAt_iff_punctured_nhds.mp ?_)
  exact ContinuousAt.comp' (by simp [continuousAt_Gamma_one]) (continuous_add_const 1).continuousAt

theorem not_continuousAt_Gamma_zero : ¬ ContinuousAt Gamma 0 :=
  tendsto_self_mul_Gamma_nhds_zero.not_tendsto (by simp) ∘
    continuousAt_iff_punctured_nhds.mp ∘ continuousAt_id.mul

theorem not_differentiableAt_Gamma_zero : ¬ DifferentiableAt ℂ Gamma 0 :=
  mt DifferentiableAt.continuousAt not_continuousAt_Gamma_zero

theorem not_continuousAt_Gamma_neg_nat (n : ℕ) : ¬ ContinuousAt Gamma (-n) := by
  induction n
  case zero =>
    rw [Nat.cast_zero, neg_zero]
    exact not_continuousAt_Gamma_zero
  case succ n ih =>
    contrapose ih
    rw [Nat.cast_add, Nat.cast_one] at ih
    suffices ContinuousAt (fun s ↦ Gamma (s - 1 + 1)) (-n) by simpa using this
    suffices ContinuousAt (fun s ↦ Gamma (s + 1)) (-n - 1) from
      this.comp' (f := fun s ↦ s - 1) (continuous_sub_right 1).continuousAt
    rw [← neg_add']
    have h0 : -(n + 1) ≠ (0 : ℂ) := neg_ne_zero.mpr n.cast_add_one_ne_zero
    exact ((continuousAt_id.mul ih).continuousWithinAt.congr Gamma_add_one
      (Gamma_add_one (-(n + 1)) h0)).continuousAt (compl_singleton_mem_nhds h0)

theorem not_differentiableAt_Gamma_neg_nat (n : ℕ) : ¬ DifferentiableAt ℂ Gamma (-n) :=
  mt DifferentiableAt.continuousAt (not_continuousAt_Gamma_neg_nat n)

theorem deriv_Gamma_add_one (s : ℂ) (hs : s ≠ 0) :
    deriv Gamma (s + 1) = Gamma s + s * deriv Gamma s := by
  by_cases! h : ∃ m : ℕ, s = -m
  · obtain ⟨m, rfl⟩ := h
    rw [← sub_neg_eq_add, ← neg_sub', ← Nat.cast_one, ← Nat.cast_sub,
      deriv_zero_of_not_differentiableAt (not_differentiableAt_Gamma_neg_nat m),
      deriv_zero_of_not_differentiableAt (not_differentiableAt_Gamma_neg_nat (m - 1)),
      Gamma_neg_nat_eq_zero, zero_add, mul_zero]
    rwa [neg_ne_zero, Nat.cast_ne_zero, ← Nat.one_le_iff_ne_zero] at hs
  · suffices HasDerivWithinAt (fun s ↦ Gamma (s + 1)) (Gamma s + s * deriv Gamma s) {0}ᶜ s by
      rw [← deriv_comp_add_const]
      exact (this.hasDerivAt (compl_singleton_mem_nhds hs)).deriv
    refine HasDerivWithinAt.congr ?_ Gamma_add_one (Gamma_add_one s hs)
    simpa using! HasDerivWithinAt.mul (hasDerivWithinAt_id s {0}ᶜ)
      (differentiableAt_Gamma s h).hasDerivAt.hasDerivWithinAt

end GammaHasDeriv

end Complex

namespace Real

open Complex MeasureTheory

theorem hasDerivAt_Gamma {s : ℝ} (hs : 0 < s) :
    HasDerivAt Gamma (∫ t in Ioi 0, t ^ (s - 1) * (log t * exp (-t))) s := by
  convert (Complex.hasDerivAt_Gamma (by simpa using hs : 0 < (s:ℂ).re)).real_of_complex
  · simp [Gamma_ofReal]
  convert (ofReal_re ?_).symm
  calc
    _ = ∫ (t : ℝ) in Ioi 0, ↑(t ^ (s - 1) * (log t * exp (-t))) := by
      refine setIntegral_congr_fun measurableSet_Ioi (fun x hx ↦ ?_)
      simp only [mem_Ioi] at hx
      norm_cast; rw [← ofReal_cpow hx.le]; norm_cast
    _ = _ := by norm_cast

theorem deriv_Gamma_one_eq_integral_log : deriv Gamma 1 = ∫ t in Ioi 0, log t * exp (-t) := by
  simpa using (hasDerivAt_Gamma (by norm_num : 0 < (1 : ℝ))).deriv

theorem integrableOn_log_log_mul_rpow {s : ℝ} (hs : 1 < s) :
    IntegrableOn (fun t ↦ log (log t) * t ^ (-s)) (Ioi 1) := by
  rw [← exp_zero, ← integrableOn_comp_exp_Ioi]
  apply Integrable.mono' (g := fun x ↦ (2 * x ^ (- (1 : ℝ) / 2) + x) * exp (-(s - 1) * x))
  · simp only [add_mul, mul_assoc]
    refine (Integrable.const_mul ?_ _).add ?_
    · simpa [IntegrableOn] using integrableOn_rpow_mul_exp_neg_mul_rpow
        (by norm_num : -1 < (-1 : ℝ) / 2) (le_refl 1) (by linarith : 0 < s - 1)
    simpa [IntegrableOn] using integrableOn_rpow_mul_exp_neg_mul_rpow
        (by norm_num : -1 < (1 : ℝ)) (le_refl 1) (by linarith : 0 < s - 1)
  · exact Measurable.aestronglyMeasurable (by fun_prop)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  simp only [mem_Ioi] at hx
  simp only [log_exp, smul_eq_mul, norm_mul, norm_eq_abs, abs_exp, neg_sub, ← exp_mul]
  rw [mul_comm, mul_assoc, ← exp_add]
  gcongr
  · rw [abs_le]; constructor
    · grw [neg_le, ← log_inv, log_le_rpow_div (by positivity) (by positivity : 0 < (1 : ℝ) / 2)]
      simp [← rpow_neg_eq_inv_rpow]; ring_nf; linarith
    grw [log_le_self hx.le, le_add_iff_nonneg_left]
    positivity
  grind

theorem deriv_Gamma_one_eq_integral_log_log {s : ℝ} (hs : 1 < s) :
    deriv Gamma 1 = (s - 1) * (∫ t in Ioi 1, log (log t) * t ^ (-s)) + log (s - 1) := by
  rw [deriv_Gamma_one_eq_integral_log, ← mul_zero (s - 1),
      ← integral_comp_mul_left_Ioi' _ _ (by linarith), ← log_one,
      ← integral_comp_log_Ioi _ zero_lt_one, smul_eq_mul]
  have hs' : s - 1 ≠ 0 := by linarith
  calc
    _ = (s - 1) * ∫ (t : ℝ) in Ioi 1, (log (log t) + log (s - 1)) * t ^ (-s) := by
      congr 1
      refine setIntegral_congr_fun measurableSet_Ioi (fun x hx ↦ ?_)
      simp only [mem_Ioi] at hx
      have : x ^ (-(s - 1)) = x ^ (-s) * x := by rw [← rpow_add_one (by positivity)]; ring_nf
      rw [log_mul hs' (log_pos hx).ne', smul_eq_mul, neg_mul_eq_neg_mul, mul_comm _ (log x),
            ← rpow_def_of_pos (by linarith), this]
      field_simp; ring
    _ = (s - 1) * ((∫ t in Ioi 1, log (log t) * t ^ (-s)) + log (s - 1) * (s - 1)⁻¹)  := by
      congr
      simp_rw [add_mul]
      convert integral_add (integrableOn_log_log_mul_rpow hs) (.const_mul ?_ _)
      · rw [integral_const_mul]; congr; symm
        convert! integral_Ioi_rpow_of_lt (a := -s) (c := 1) (by linarith) zero_lt_one using 1
        simp; grind
      exact integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
    _ = _ := by field_simp

@[fun_prop]
theorem differentiableAt_Gamma {s : ℝ} (hs : ∀ m : ℕ, s ≠ -m) : DifferentiableAt ℝ Gamma s := by
  refine (Complex.differentiableAt_Gamma _ ?_).hasDerivAt.real_of_complex.differentiableAt
  simp_rw [← ofReal_natCast, ← ofReal_neg, Ne, ofReal_inj]
  exact hs

theorem differentiableOn_Gamma_Ioi : DifferentiableOn ℝ Gamma (Ioi 0) :=
  fun _ h ↦ (differentiableAt_Gamma <| by bound [mem_Ioi.mp h]).differentiableWithinAt

end Real
