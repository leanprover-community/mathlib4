/-
Copyright (c) 2023 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

#align_import analysis.special_functions.improper_integrals from "leanprover-community/mathlib"@"fd5edc43dc4f10b85abfe544b88f82cf13c5f844"

/-!
# Evaluation of specific improper integrals

This file contains some integrability results, and evaluations of integrals, over `ℝ` or over
half-infinite intervals in `ℝ`.

## See also

- `Mathlib.Analysis.SpecialFunctions.Integrals` -- integrals over finite intervals
- `Mathlib.Analysis.SpecialFunctions.Gaussian` -- integral of `exp (-x ^ 2)`
- `Mathlib.Analysis.SpecialFunctions.JapaneseBracket`-- integrability of `(1+‖x‖)^(-r)`.
-/


open Real Set Filter MeasureTheory intervalIntegral

open scoped Topology

theorem integrableOn_exp_Iic (c : ℝ) : IntegrableOn exp (Iic c) := by
  refine'
    integrableOn_Iic_of_intervalIntegral_norm_bounded (exp c) c
      (fun y => intervalIntegrable_exp.1) tendsto_id
      (eventually_of_mem (Iic_mem_atBot 0) fun y _ => _)
  simp_rw [norm_of_nonneg (exp_pos _).le, integral_exp, sub_le_self_iff]
  exact (exp_pos _).le
#align integrable_on_exp_Iic integrableOn_exp_Iic

theorem integral_exp_Iic (c : ℝ) : ∫ x : ℝ in Iic c, exp x = exp c := by
  refine'
    tendsto_nhds_unique
      (intervalIntegral_tendsto_integral_Iic _ (integrableOn_exp_Iic _) tendsto_id) _
  simp_rw [integral_exp, show 𝓝 (exp c) = 𝓝 (exp c - 0) by rw [sub_zero]]
  exact tendsto_exp_atBot.const_sub _
#align integral_exp_Iic integral_exp_Iic

theorem integral_exp_Iic_zero : ∫ x : ℝ in Iic 0, exp x = 1 :=
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
    IntegrableOn (fun t : ℝ => t ^ a) (Ioi c) := by
  have hd : ∀ (x : ℝ) (_ : x ∈ Ici c), HasDerivAt (fun t => t ^ (a + 1) / (a + 1)) (x ^ a) x := by
    intro x hx
    -- Porting note: helped `convert` with explicit arguments
    convert (hasDerivAt_rpow_const (p := a + 1) (Or.inl (hc.trans_le hx).ne')).div_const _ using 1
    field_simp [show a + 1 ≠ 0 from ne_of_lt (by linarith), mul_comm]
  have ht : Tendsto (fun t => t ^ (a + 1) / (a + 1)) atTop (𝓝 (0 / (a + 1))) := by
    apply Tendsto.div_const
    simpa only [neg_neg] using tendsto_rpow_neg_atTop (by linarith : 0 < -(a + 1))
  exact
    integrableOn_Ioi_deriv_of_nonneg' hd (fun t ht => rpow_nonneg_of_nonneg (hc.trans ht).le a) ht
#align integrable_on_Ioi_rpow_of_lt integrableOn_Ioi_rpow_of_lt

theorem integrableOn_Ioi_rpow_iff {s t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun x ↦ x ^ s) (Ioi t) ↔ s < -1 := by
  refine ⟨fun h ↦ ?_, fun h ↦ integrableOn_Ioi_rpow_of_lt h ht⟩
  contrapose! h
  intro H
  have H' : IntegrableOn (fun x ↦ x ^ s) (Ioi (max 1 t)) :=
    H.mono (Set.Ioi_subset_Ioi (le_max_right _ _)) le_rfl
  have : IntegrableOn (fun x ↦ x⁻¹) (Ioi (max 1 t)) := by
    apply H'.mono' measurable_inv.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have x_one : 1 ≤ x := ((le_max_left _ _).trans_lt (mem_Ioi.1 hx)).le
    simp only [norm_inv, Real.norm_eq_abs, abs_of_nonneg (zero_le_one.trans x_one)]
    rw [← Real.rpow_neg_one x]
    exact Real.rpow_le_rpow_of_exponent_le x_one h
  exact not_IntegrableOn_Ioi_inv this

/-- The real power function with any exponent is not integrable on `(0, +∞)`. -/
theorem not_integrableOn_Ioi_rpow (s : ℝ) : ¬ IntegrableOn (fun x ↦ x ^ s) (Ioi (0 : ℝ)) := by
  intro h
  rcases le_or_lt s (-1) with hs|hs
  · have : IntegrableOn (fun x ↦ x ^ s) (Ioo (0 : ℝ) 1) := h.mono Ioo_subset_Ioi_self le_rfl
    rw [integrableOn_Ioo_rpow_iff zero_lt_one] at this
    exact hs.not_lt this
  · have : IntegrableOn (fun x ↦ x ^ s) (Ioi 1) := h.mono (Ioi_subset_Ioi zero_le_one) le_rfl
    rw [integrableOn_Ioi_rpow_iff zero_lt_one] at this
    exact hs.not_lt this

theorem setIntegral_Ioi_zero_rpow (s : ℝ) : ∫ x in Ioi (0 : ℝ), x ^ s = 0 :=
  MeasureTheory.integral_undef (not_integrableOn_Ioi_rpow s)

theorem integral_Ioi_rpow_of_lt {a : ℝ} (ha : a < -1) {c : ℝ} (hc : 0 < c) :
    ∫ t : ℝ in Ioi c, t ^ a = -c ^ (a + 1) / (a + 1) := by
  have hd : ∀ (x : ℝ) (_ : x ∈ Ici c), HasDerivAt (fun t => t ^ (a + 1) / (a + 1)) (x ^ a) x := by
    intro x hx
    convert (hasDerivAt_rpow_const (p := a + 1) (Or.inl (hc.trans_le hx).ne')).div_const _ using 1
    field_simp [show a + 1 ≠ 0 from ne_of_lt (by linarith), mul_comm]
  have ht : Tendsto (fun t => t ^ (a + 1) / (a + 1)) atTop (𝓝 (0 / (a + 1))) := by
    apply Tendsto.div_const
    simpa only [neg_neg] using tendsto_rpow_neg_atTop (by linarith : 0 < -(a + 1))
  convert integral_Ioi_of_hasDerivAt_of_tendsto' hd (integrableOn_Ioi_rpow_of_lt ha hc) ht using 1
  simp only [neg_div, zero_div, zero_sub]
#align integral_Ioi_rpow_of_lt integral_Ioi_rpow_of_lt

theorem integrableOn_Ioi_cpow_of_lt {a : ℂ} (ha : a.re < -1) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ a) (Ioi c) := by
  rw [IntegrableOn, ← integrable_norm_iff, ← IntegrableOn]
  refine' (integrableOn_Ioi_rpow_of_lt ha hc).congr_fun (fun x hx => _) measurableSet_Ioi
  · dsimp only
    rw [Complex.norm_eq_abs, Complex.abs_cpow_eq_rpow_re_of_pos (hc.trans hx)]
  · refine' ContinuousOn.aestronglyMeasurable (fun t ht => _) measurableSet_Ioi
    exact
      (Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr (hc.trans ht).ne')).continuousWithinAt
#align integrable_on_Ioi_cpow_of_lt integrableOn_Ioi_cpow_of_lt

theorem integrableOn_Ioi_cpow_iff {s : ℂ} {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun x : ℝ ↦ (x : ℂ) ^ s) (Ioi t) ↔ s.re < -1 := by
  refine ⟨fun h ↦ ?_, fun h ↦ integrableOn_Ioi_cpow_of_lt h ht⟩
  have B : IntegrableOn (fun a ↦ a ^ s.re) (Ioi t) := by
    apply (integrableOn_congr_fun _ measurableSet_Ioi).1 h.norm
    intro a ha
    have : 0 < a := ht.trans ha
    simp [Complex.abs_cpow_eq_rpow_re_of_pos this]
  rwa [integrableOn_Ioi_rpow_iff ht] at B

/-- The complex power function with any exponent is not integrable on `(0, +∞)`. -/
theorem not_integrableOn_Ioi_cpow (s : ℂ) :
    ¬ IntegrableOn (fun x : ℝ ↦ (x : ℂ) ^ s) (Ioi (0 : ℝ)) := by
  intro h
  rcases le_or_lt s.re (-1) with hs|hs
  · have : IntegrableOn (fun x : ℝ ↦ (x : ℂ) ^ s) (Ioo (0 : ℝ) 1) :=
      h.mono Ioo_subset_Ioi_self le_rfl
    rw [integrableOn_Ioo_cpow_iff zero_lt_one] at this
    exact hs.not_lt this
  · have : IntegrableOn (fun x : ℝ ↦ (x : ℂ) ^ s) (Ioi 1) :=
      h.mono (Ioi_subset_Ioi zero_le_one) le_rfl
    rw [integrableOn_Ioi_cpow_iff zero_lt_one] at this
    exact hs.not_lt this

theorem setIntegral_Ioi_zero_cpow (s : ℂ) : ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ s = 0 :=
  MeasureTheory.integral_undef (not_integrableOn_Ioi_cpow s)

theorem integral_Ioi_cpow_of_lt {a : ℂ} (ha : a.re < -1) {c : ℝ} (hc : 0 < c) :
    (∫ t : ℝ in Ioi c, (t : ℂ) ^ a) = -(c : ℂ) ^ (a + 1) / (a + 1) := by
  refine'
    tendsto_nhds_unique
      (intervalIntegral_tendsto_integral_Ioi c (integrableOn_Ioi_cpow_of_lt ha hc) tendsto_id) _
  suffices
    Tendsto (fun x : ℝ => ((x : ℂ) ^ (a + 1) - (c : ℂ) ^ (a + 1)) / (a + 1)) atTop
      (𝓝 <| -c ^ (a + 1) / (a + 1)) by
    refine' this.congr' ((eventually_gt_atTop 0).mp (eventually_of_forall fun x hx => _))
    dsimp only
    rw [integral_cpow, id.def]
    refine' Or.inr ⟨_, not_mem_uIcc_of_lt hc hx⟩
    apply_fun Complex.re
    rw [Complex.neg_re, Complex.one_re]
    exact ha.ne
  simp_rw [← zero_sub, sub_div]
  refine' (Tendsto.div_const _ _).sub_const _
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine'
    (tendsto_rpow_neg_atTop (by linarith : 0 < -(a.re + 1))).congr'
      ((eventually_gt_atTop 0).mp (eventually_of_forall fun x hx => _))
  simp_rw [neg_neg, Complex.norm_eq_abs, Complex.abs_cpow_eq_rpow_re_of_pos hx, Complex.add_re,
    Complex.one_re]
#align integral_Ioi_cpow_of_lt integral_Ioi_cpow_of_lt
