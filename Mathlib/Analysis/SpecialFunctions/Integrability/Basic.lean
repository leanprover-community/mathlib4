/-
Copyright (c) 2021 Benjamin Davidson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Davidson
-/
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.NonIntegrable
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Integrability of Special Functions

This file establishes basic facts about the interval integrability of special functions, including
powers and the logarithm.
-/

open Interval MeasureTheory Real Set

variable {a b c d : ℝ} (n : ℕ) {f : ℝ → ℝ} {μ : Measure ℝ} [IsLocallyFiniteMeasure μ]

namespace intervalIntegral

@[simp]
theorem intervalIntegrable_pow : IntervalIntegrable (fun x => x ^ n) μ a b :=
  (continuous_pow n).intervalIntegrable a b

theorem intervalIntegrable_zpow {n : ℤ} (h : 0 ≤ n ∨ (0 : ℝ) ∉ [[a, b]]) :
    IntervalIntegrable (fun x => x ^ n) μ a b :=
  (continuousOn_id.zpow₀ n fun _ hx => h.symm.imp (ne_of_mem_of_not_mem hx) id).intervalIntegrable

/-- See `intervalIntegrable_rpow'` for a version with a weaker hypothesis on `r`, but assuming the
measure is volume. -/
theorem intervalIntegrable_rpow {r : ℝ} (h : 0 ≤ r ∨ (0 : ℝ) ∉ [[a, b]]) :
    IntervalIntegrable (fun x => x ^ r) μ a b :=
  (continuousOn_id.rpow_const fun _ hx =>
    h.symm.imp (ne_of_mem_of_not_mem hx) id).intervalIntegrable

/-- See `intervalIntegrable_rpow` for a version applying to any locally finite measure, but with a
stronger hypothesis on `r`. -/
theorem intervalIntegrable_rpow' {r : ℝ} (h : -1 < r) :
    IntervalIntegrable (fun x => x ^ r) volume a b := by
  suffices ∀ c : ℝ, IntervalIntegrable (fun x => x ^ r) volume 0 c by
    exact IntervalIntegrable.trans (this a).symm (this b)
  have : ∀ c : ℝ, 0 ≤ c → IntervalIntegrable (fun x => x ^ r) volume 0 c := by
    intro c hc
    rw [intervalIntegrable_iff, uIoc_of_le hc]
    have hderiv : ∀ x ∈ Ioo 0 c, HasDerivAt (fun x : ℝ => x ^ (r + 1) / (r + 1)) (x ^ r) x := by
      intro x hx
      convert (Real.hasDerivAt_rpow_const (p := r + 1) (Or.inl hx.1.ne')).div_const (r + 1) using 1
      field_simp [(by linarith : r + 1 ≠ 0)]
    apply integrableOn_deriv_of_nonneg _ hderiv
    · intro x hx; apply rpow_nonneg hx.1.le
    · refine (continuousOn_id.rpow_const ?_).div_const _; intro x _; right; linarith
  intro c; rcases le_total 0 c with (hc | hc)
  · exact this c hc
  · rw [IntervalIntegrable.iff_comp_neg, neg_zero]
    have m := (this (-c) (by linarith)).smul (cos (r * π))
    rw [intervalIntegrable_iff] at m ⊢
    refine m.congr_fun ?_ measurableSet_Ioc; intro x hx
    rw [uIoc_of_le (by linarith : 0 ≤ -c)] at hx
    simp only [Pi.smul_apply, Algebra.id.smul_eq_mul, log_neg_eq_log, mul_comm,
      rpow_def_of_pos hx.1, rpow_def_of_neg (by linarith [hx.1] : -x < 0)]

/-- The power function `x ↦ x^s` is integrable on `(0, t)` iff `-1 < s`. -/
lemma integrableOn_Ioo_rpow_iff {s t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun x ↦ x ^ s) (Ioo (0 : ℝ) t) ↔ -1 < s := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  swap
  · rw [← intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le]
    apply intervalIntegrable_rpow' h (a := 0) (b := t)
  contrapose! h
  intro H
  have I : 0 < min 1 t := lt_min zero_lt_one ht
  have H' : IntegrableOn (fun x ↦ x ^ s) (Ioo 0 (min 1 t)) :=
    H.mono (Set.Ioo_subset_Ioo le_rfl (min_le_right _ _)) le_rfl
  have : IntegrableOn (fun x ↦ x⁻¹) (Ioo 0 (min 1 t)) := by
    apply H'.mono' measurable_inv.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    simp only [norm_inv, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hx.1)]
    rwa [← Real.rpow_neg_one x, Real.rpow_le_rpow_left_iff_of_base_lt_one hx.1]
    exact lt_of_lt_of_le hx.2 (min_le_left _ _)
  have : IntervalIntegrable (fun x ↦ x⁻¹) volume 0 (min 1 t) := by
    rwa [intervalIntegrable_iff_integrableOn_Ioo_of_le I.le]
  simp [intervalIntegrable_inv_iff, I.ne] at this

/-- See `intervalIntegrable_cpow'` for a version with a weaker hypothesis on `r`, but assuming the
measure is volume. -/
theorem intervalIntegrable_cpow {r : ℂ} (h : 0 ≤ r.re ∨ (0 : ℝ) ∉ [[a, b]]) :
    IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ r) μ a b := by
  by_cases h2 : (0 : ℝ) ∉ [[a, b]]
  · -- Easy case #1: 0 ∉ [a, b] -- use continuity.
    refine (continuousOn_of_forall_continuousAt fun x hx => ?_).intervalIntegrable
    exact Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr <| ne_of_mem_of_not_mem hx h2)
  rw [eq_false h2, or_false] at h
  rcases lt_or_eq_of_le h with (h' | h')
  · -- Easy case #2: 0 < re r -- again use continuity
    exact (Complex.continuous_ofReal_cpow_const h').intervalIntegrable _ _
  -- Now the hard case: re r = 0 and 0 is in the interval.
  refine (IntervalIntegrable.intervalIntegrable_norm_iff ?_).mp ?_
  · refine (measurable_of_continuousOn_compl_singleton (0 : ℝ) ?_).aestronglyMeasurable
    exact continuousOn_of_forall_continuousAt fun x hx =>
      Complex.continuousAt_ofReal_cpow_const x r (Or.inr hx)
  -- reduce to case of integral over `[0, c]`
  suffices ∀ c : ℝ, IntervalIntegrable (fun x : ℝ => ‖(x : ℂ) ^ r‖) μ 0 c from
    (this a).symm.trans (this b)
  intro c
  rcases le_or_gt 0 c with (hc | hc)
  · -- case `0 ≤ c`: integrand is identically 1
    have : IntervalIntegrable (fun _ => 1 : ℝ → ℝ) μ 0 c := intervalIntegrable_const
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hc] at this ⊢
    refine IntegrableOn.congr_fun this (fun x hx => ?_) measurableSet_Ioc
    dsimp only
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx.1, ← h', rpow_zero]
  · -- case `c < 0`: integrand is identically constant, *except* at `x = 0` if `r ≠ 0`.
    apply IntervalIntegrable.symm
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hc.le]
    rw [← Ioo_union_right hc, integrableOn_union, and_comm]; constructor
    · exact integrableOn_singleton (by simp) <|
        isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure.lt_top_of_isCompact isCompact_singleton
    · have : ∀ x : ℝ, x ∈ Ioo c 0 → ‖Complex.exp (↑π * Complex.I * r)‖ = ‖(x : ℂ) ^ r‖ := by
        intro x hx
        rw [Complex.ofReal_cpow_of_nonpos hx.2.le, norm_mul, ← Complex.ofReal_neg,
          Complex.norm_cpow_eq_rpow_re_of_pos (neg_pos.mpr hx.2), ← h',
          rpow_zero, one_mul]
      refine IntegrableOn.congr_fun ?_ this measurableSet_Ioo
      rw [integrableOn_const_iff]
      right
      refine (measure_mono Set.Ioo_subset_Icc_self).trans_lt ?_
      exact isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure.lt_top_of_isCompact isCompact_Icc

/-- See `intervalIntegrable_cpow` for a version applying to any locally finite measure, but with a
stronger hypothesis on `r`. -/
theorem intervalIntegrable_cpow' {r : ℂ} (h : -1 < r.re) :
    IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ r) volume a b := by
  suffices ∀ c : ℝ, IntervalIntegrable (fun x => (x : ℂ) ^ r) volume 0 c by
    exact IntervalIntegrable.trans (this a).symm (this b)
  have : ∀ c : ℝ, 0 ≤ c → IntervalIntegrable (fun x => (x : ℂ) ^ r) volume 0 c := by
    intro c hc
    rw [← IntervalIntegrable.intervalIntegrable_norm_iff]
    · rw [intervalIntegrable_iff]
      apply IntegrableOn.congr_fun
      · rw [← intervalIntegrable_iff]; exact intervalIntegral.intervalIntegrable_rpow' h
      · intro x hx
        rw [uIoc_of_le hc] at hx
        dsimp only
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hx.1]
      · exact measurableSet_uIoc
    · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_uIoc
      refine continuousOn_of_forall_continuousAt fun x hx => ?_
      rw [uIoc_of_le hc] at hx
      refine (continuousAt_cpow_const (Or.inl ?_)).comp Complex.continuous_ofReal.continuousAt
      rw [Complex.ofReal_re]
      exact hx.1
  intro c; rcases le_total 0 c with (hc | hc)
  · exact this c hc
  · rw [IntervalIntegrable.iff_comp_neg, neg_zero]
    have m := (this (-c) (by linarith)).const_mul (Complex.exp (π * Complex.I * r))
    rw [intervalIntegrable_iff, uIoc_of_le (by linarith : 0 ≤ -c)] at m ⊢
    refine m.congr_fun (fun x hx => ?_) measurableSet_Ioc
    dsimp only
    have : -x ≤ 0 := by linarith [hx.1]
    rw [Complex.ofReal_cpow_of_nonpos this, mul_comm]
    simp

/-- The complex power function `x ↦ x^s` is integrable on `(0, t)` iff `-1 < s.re`. -/
theorem integrableOn_Ioo_cpow_iff {s : ℂ} {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun x : ℝ ↦ (x : ℂ) ^ s) (Ioo (0 : ℝ) t) ↔ -1 < s.re := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  swap
  · rw [← intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le]
    exact intervalIntegrable_cpow' h (a := 0) (b := t)
  have B : IntegrableOn (fun a ↦ a ^ s.re) (Ioo 0 t) := by
    apply (integrableOn_congr_fun _ measurableSet_Ioo).1 h.norm
    intro a ha
    simp [Complex.norm_cpow_eq_rpow_re_of_pos ha.1]
  rwa [integrableOn_Ioo_rpow_iff ht] at B

@[simp]
theorem intervalIntegrable_id : IntervalIntegrable (fun x => x) μ a b :=
  continuous_id.intervalIntegrable a b

theorem intervalIntegrable_const : IntervalIntegrable (fun _ => c) μ a b :=
  continuous_const.intervalIntegrable a b

theorem intervalIntegrable_one_div (h : ∀ x : ℝ, x ∈ [[a, b]] → f x ≠ 0)
    (hf : ContinuousOn f [[a, b]]) : IntervalIntegrable (fun x => 1 / f x) μ a b :=
  (continuousOn_const.div hf h).intervalIntegrable

@[simp]
theorem intervalIntegrable_inv (h : ∀ x : ℝ, x ∈ [[a, b]] → f x ≠ 0)
    (hf : ContinuousOn f [[a, b]]) : IntervalIntegrable (fun x => (f x)⁻¹) μ a b := by
  simpa only [one_div] using intervalIntegrable_one_div h hf

@[simp]
theorem intervalIntegrable_sin : IntervalIntegrable sin μ a b :=
  continuous_sin.intervalIntegrable a b

@[simp]
theorem intervalIntegrable_cos : IntervalIntegrable cos μ a b :=
  continuous_cos.intervalIntegrable a b

@[simp]
theorem intervalIntegrable_exp : IntervalIntegrable exp μ a b :=
  continuous_exp.intervalIntegrable a b

@[simp]
theorem _root_.IntervalIntegrable.log (hf : ContinuousOn f [[a, b]])
    (h : ∀ x : ℝ, x ∈ [[a, b]] → f x ≠ 0) :
    IntervalIntegrable (fun x => log (f x)) μ a b :=
  (ContinuousOn.log hf h).intervalIntegrable

/--
The real logarithm is interval integrable (with respect to every locally finite measure) over every
interval that does not contain zero. See `intervalIntegrable_log'` for a version without any
hypothesis on the interval, but assuming the measure is the volume.
-/
@[simp]
theorem intervalIntegrable_log (h : (0 : ℝ) ∉ [[a, b]]) : IntervalIntegrable log μ a b :=
  IntervalIntegrable.log continuousOn_id fun _ hx => ne_of_mem_of_not_mem hx h

/--
The real logarithm is interval integrable (with respect to the volume measure) on every interval.
See `intervalIntegrable_log` for a version applying to any locally finite measure, but with an
additional hypothesis on the interval.
-/
@[simp]
theorem intervalIntegrable_log' : IntervalIntegrable log volume a b := by
  -- Log is even, so it suffices to consider the case 0 < a and b = 0
  apply intervalIntegrable_of_even (log_neg_eq_log · |>.symm)
  intro x hx
  -- Split integral
  apply IntervalIntegrable.trans (b := 1)
  · -- Show integrability on [0…1] using non-negativity of the derivative
    rw [← neg_neg log]
    apply IntervalIntegrable.neg
    apply intervalIntegrable_deriv_of_nonneg (g := fun x ↦ -(x * log x - x))
    · exact (continuous_mul_log.continuousOn.sub continuous_id.continuousOn).neg
    · intro s ⟨hs, _⟩
      norm_num at *
      simpa using (hasDerivAt_id s).sub (hasDerivAt_mul_log hs.ne.symm)
    · intro s ⟨hs₁, hs₂⟩
      norm_num at *
      exact (log_nonpos_iff hs₁.le).mpr hs₂.le
  · -- Show integrability on [1…t] by continuity
    apply ContinuousOn.intervalIntegrable
    apply Real.continuousOn_log.mono
    apply Set.notMem_uIcc_of_lt zero_lt_one at hx
    simpa

theorem intervalIntegrable_one_div_one_add_sq :
    IntervalIntegrable (fun x : ℝ => 1 / (↑1 + x ^ 2)) μ a b := by
  refine (continuous_const.div ?_ fun x => ?_).intervalIntegrable a b
  · fun_prop
  · nlinarith

@[simp]
theorem intervalIntegrable_inv_one_add_sq :
    IntervalIntegrable (fun x : ℝ => (↑1 + x ^ 2)⁻¹) μ a b := by
  field_simp [mod_cast intervalIntegrable_one_div_one_add_sq]

end intervalIntegral
