/-
Copyright (c) 2023 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler

! This file was ported from Lean 3 source module analysis.special_functions.improper_integrals
! leanprover-community/mathlib commit fd5edc43dc4f10b85abfe544b88f82cf13c5f844
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.SpecialFunctions.Integrals
import Mathbin.MeasureTheory.Group.Integration
import Mathbin.MeasureTheory.Integral.ExpDecay
import Mathbin.MeasureTheory.Integral.IntegralEqImproper
import Mathbin.MeasureTheory.Measure.Lebesgue.Integral

/-!
# Evaluation of specific improper integrals

This file contains some integrability results, and evaluations of integrals, over `ℝ` or over
half-infinite intervals in `ℝ`.

## See also

- `analysis.special_functions.integrals` -- integrals over finite intervals
- `analysis.special_functions.gaussian` -- integral of `exp (-x ^ 2)`
- `analysis.special_functions.japanese_bracket`-- integrability of `(1+‖x‖)^(-r)`.
-/


open Real Set Filter MeasureTheory intervalIntegral

open scoped Topology

theorem integrableOn_exp_Iic (c : ℝ) : IntegrableOn exp (Iic c) :=
  by
  refine'
    integrable_on_Iic_of_interval_integral_norm_bounded (exp c) c
      (fun y => interval_integrable_exp.1) tendsto_id
      (eventually_of_mem (Iic_mem_at_bot 0) fun y hy => _)
  simp_rw [norm_of_nonneg (exp_pos _).le, integral_exp, sub_le_self_iff]
  exact (exp_pos _).le
#align integrable_on_exp_Iic integrableOn_exp_Iic

theorem integral_exp_Iic (c : ℝ) : (∫ x : ℝ in Iic c, exp x) = exp c :=
  by
  refine'
    tendsto_nhds_unique
      (interval_integral_tendsto_integral_Iic _ (integrableOn_exp_Iic _) tendsto_id) _
  simp_rw [integral_exp, show 𝓝 (exp c) = 𝓝 (exp c - 0) by rw [sub_zero]]
  exact tendsto_exp_at_bot.const_sub _
#align integral_exp_Iic integral_exp_Iic

theorem integral_exp_Iic_zero : (∫ x : ℝ in Iic 0, exp x) = 1 :=
  exp_zero ▸ integral_exp_Iic 0
#align integral_exp_Iic_zero integral_exp_Iic_zero

theorem integral_exp_neg_Ioi (c : ℝ) : (∫ x : ℝ in Ioi c, exp (-x)) = exp (-c) := by
  simpa only [integral_comp_neg_Ioi] using integral_exp_Iic (-c)
#align integral_exp_neg_Ioi integral_exp_neg_Ioi

theorem integral_exp_neg_Ioi_zero : (∫ x : ℝ in Ioi 0, exp (-x)) = 1 := by
  simpa only [neg_zero, exp_zero] using integral_exp_neg_Ioi 0
#align integral_exp_neg_Ioi_zero integral_exp_neg_Ioi_zero

/-- If `0 < c`, then `(λ t : ℝ, t ^ a)` is integrable on `(c, ∞)` for all `a < -1`. -/
theorem integrableOn_Ioi_rpow_of_lt {a : ℝ} (ha : a < -1) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => t ^ a) (Ioi c) :=
  by
  have hd : ∀ (x : ℝ) (hx : x ∈ Ici c), HasDerivAt (fun t => t ^ (a + 1) / (a + 1)) (x ^ a) x :=
    by
    intro x hx
    convert (has_deriv_at_rpow_const (Or.inl (hc.trans_le hx).ne')).div_const _
    field_simp [show a + 1 ≠ 0 from ne_of_lt (by linarith), mul_comm]
  have ht : tendsto (fun t => t ^ (a + 1) / (a + 1)) at_top (𝓝 (0 / (a + 1))) :=
    by
    apply tendsto.div_const
    simpa only [neg_neg] using tendsto_rpow_neg_atTop (by linarith : 0 < -(a + 1))
  exact
    integrable_on_Ioi_deriv_of_nonneg' hd (fun t ht => rpow_nonneg_of_nonneg (hc.trans ht).le a) ht
#align integrable_on_Ioi_rpow_of_lt integrableOn_Ioi_rpow_of_lt

theorem integral_Ioi_rpow_of_lt {a : ℝ} (ha : a < -1) {c : ℝ} (hc : 0 < c) :
    (∫ t : ℝ in Ioi c, t ^ a) = -c ^ (a + 1) / (a + 1) :=
  by
  have hd : ∀ (x : ℝ) (hx : x ∈ Ici c), HasDerivAt (fun t => t ^ (a + 1) / (a + 1)) (x ^ a) x :=
    by
    intro x hx
    convert (has_deriv_at_rpow_const (Or.inl (hc.trans_le hx).ne')).div_const _
    field_simp [show a + 1 ≠ 0 from ne_of_lt (by linarith), mul_comm]
  have ht : tendsto (fun t => t ^ (a + 1) / (a + 1)) at_top (𝓝 (0 / (a + 1))) :=
    by
    apply tendsto.div_const
    simpa only [neg_neg] using tendsto_rpow_neg_atTop (by linarith : 0 < -(a + 1))
  convert integral_Ioi_of_has_deriv_at_of_tendsto' hd (integrableOn_Ioi_rpow_of_lt ha hc) ht
  simp only [neg_div, zero_div, zero_sub]
#align integral_Ioi_rpow_of_lt integral_Ioi_rpow_of_lt

theorem integrableOn_Ioi_cpow_of_lt {a : ℂ} (ha : a.re < -1) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ a) (Ioi c) :=
  by
  rw [integrable_on, ← integrable_norm_iff, ← integrable_on]
  refine' (integrableOn_Ioi_rpow_of_lt ha hc).congr_fun (fun x hx => _) measurableSet_Ioi
  · dsimp only
    rw [Complex.norm_eq_abs, Complex.abs_cpow_eq_rpow_re_of_pos (hc.trans hx)]
  · refine' ContinuousOn.aestronglyMeasurable (fun t ht => _) measurableSet_Ioi
    exact
      (Complex.continuousAt_of_real_cpow_const _ _ (Or.inr (hc.trans ht).ne')).ContinuousWithinAt
#align integrable_on_Ioi_cpow_of_lt integrableOn_Ioi_cpow_of_lt

theorem integral_Ioi_cpow_of_lt {a : ℂ} (ha : a.re < -1) {c : ℝ} (hc : 0 < c) :
    (∫ t : ℝ in Ioi c, (t : ℂ) ^ a) = -(c : ℂ) ^ (a + 1) / (a + 1) :=
  by
  refine'
    tendsto_nhds_unique
      (interval_integral_tendsto_integral_Ioi c (integrableOn_Ioi_cpow_of_lt ha hc) tendsto_id) _
  suffices
    tendsto (fun x : ℝ => ((x : ℂ) ^ (a + 1) - (c : ℂ) ^ (a + 1)) / (a + 1)) at_top
      (𝓝 <| -c ^ (a + 1) / (a + 1))
    by
    refine' this.congr' ((eventually_gt_at_top 0).mp (eventually_of_forall fun x hx => _))
    rw [integral_cpow, id.def]
    refine' Or.inr ⟨_, not_mem_uIcc_of_lt hc hx⟩
    apply_fun Complex.re
    rw [Complex.neg_re, Complex.one_re]
    exact ha.ne
  simp_rw [← zero_sub, sub_div]
  refine' (tendsto.div_const _ _).sub_const _
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine'
    (tendsto_rpow_neg_atTop (by linarith : 0 < -(a.re + 1))).congr'
      ((eventually_gt_at_top 0).mp (eventually_of_forall fun x hx => _))
  simp_rw [neg_neg, Complex.norm_eq_abs, Complex.abs_cpow_eq_rpow_re_of_pos hx, Complex.add_re,
    Complex.one_re]
#align integral_Ioi_cpow_of_lt integral_Ioi_cpow_of_lt

