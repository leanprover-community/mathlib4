/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Measure.IntegralCharFun
import Mathlib.MeasureTheory.Measure.TightNormed

/-!
# TightCharFun

Tightness from convergence of characteristic functions.

## Main statements

* `isTightMeasureSet_of_tendsto_charFun`: if the characteristic functions of a sequence of measures
 `μ : ℕ → Measure E` on a finite dimensional inner product space converge pointwise
  to a function which is continuous at 0, then `{μ n | n}` is tight.

-/

open Filter
open scoped Topology RealInnerProductSpace ENNReal

namespace MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- If the characteristic functions of a sequence of measures `μ : ℕ → Measure E` converge pointwise
to a function which is continuous at 0, then `{μ n | n}` is tight. -/
lemma isTightMeasureSet_of_tendsto_charFun {μ : ℕ → Measure E} [∀ i, IsProbabilityMeasure (μ i)]
    {f : E → ℂ} (hf : ContinuousAt f 0) (hf_meas : Measurable f)
    (h : ∀ t, Tendsto (fun n ↦ charFun (μ n) t) atTop (𝓝 (f t))) :
    IsTightMeasureSet (Set.range μ) := by
  refine isTightMeasureSet_range_of_tendsto_limsup_inner_of_norm_eq_one ℝ fun z hz ↦ ?_
  suffices Tendsto (fun r : ℝ ↦ limsup (fun n ↦ (μ n).real {x | r < |⟪z, x⟫|}) atTop) atTop (𝓝 0) by
    have h_ofReal (r : ℝ) : limsup (fun n ↦ μ n {x | r < |⟪z, x⟫|}) atTop
        = ENNReal.ofReal (limsup (fun n ↦ (μ n).real {x | r < |⟪z, x⟫|}) atTop) := by
      simp_rw [measureReal_def,
        ENNReal.limsup_toReal_eq (b := 1) (by simp) (.of_forall fun _ ↦ prob_le_one)]
      rw [ENNReal.ofReal_toReal]
      refine ne_top_of_le_ne_top (by simp : 1 ≠ ∞) ?_
      refine limsup_le_of_le ?_ (.of_forall fun _ ↦ prob_le_one)
      exact IsCoboundedUnder.of_frequently_ge <| .of_forall fun _ ↦ zero_le _
    simp only [Real.norm_eq_abs, h_ofReal]
    rw [← ENNReal.ofReal_zero]
    exact ENNReal.tendsto_ofReal this
  have h_le_4 n r (hr : 0 < r) :
      2⁻¹ * r * ‖∫ t in -2 * r⁻¹..2 * r⁻¹, 1 - charFun (μ n) (t • z)‖ ≤ 4 := by
    have hr' : -(2 * r⁻¹) ≤ 2 * r⁻¹ := by rw [neg_le_self_iff]; positivity
    calc 2⁻¹ * r * ‖∫ t in -2 * r⁻¹..2 * r⁻¹, 1 - charFun (μ n) (t • z)‖
    _ ≤ 2⁻¹ * r * ∫ t in -(2 * r⁻¹)..2 * r⁻¹, ‖1 - charFun (μ n) (t • z)‖ := by
      simp only [neg_mul]
      gcongr
      rw [intervalIntegral.integral_of_le hr', intervalIntegral.integral_of_le hr']
      exact norm_integral_le_integral_norm _
    _ ≤ 2⁻¹ * r * ∫ t in -(2 * r⁻¹)..2 * r⁻¹, 2 := by
      gcongr
      rw [intervalIntegral.integral_of_le hr', intervalIntegral.integral_of_le hr']
      refine integral_mono_of_nonneg ?_ (by fun_prop) ?_
      · exact ae_of_all _ fun _ ↦ by positivity
      · refine ae_of_all _ fun x ↦ norm_one_sub_charFun_le_two
    _ ≤ 4 := by
      simp only [intervalIntegral.integral_const, sub_neg_eq_add, smul_eq_mul]
      ring_nf
      rw [mul_inv_cancel₀ hr.ne', one_mul]
  have h_le n r := measureReal_abs_inner_gt_le_integral_charFun (μ := μ n) (a := z) (r := r)
  -- We introduce an upper bound for the limsup.
  -- This is where we use the fact that `charFun (μ n)` converges to `f`.
  have h_limsup_le r (hr : 0 < r) :
      limsup (fun n ↦ (μ n).real {x | r < |⟪z, x⟫|}) atTop
        ≤ 2⁻¹ * r * ‖∫ t in -2 * r⁻¹..2 * r⁻¹, 1 - f (t • z)‖ := by
    calc limsup (fun n ↦ (μ n).real {x | r < |⟪z, x⟫|}) atTop
    _ ≤ limsup (fun n ↦ 2⁻¹ * r
        * ‖∫ t in -2 * r⁻¹..2 * r⁻¹, 1 - charFun (μ n) (t • z)‖) atTop := by
      refine limsup_le_limsup (.of_forall fun n ↦ h_le n r hr) ?_ ?_
      · exact IsCoboundedUnder.of_frequently_ge <| .of_forall fun _ ↦ ENNReal.toReal_nonneg
      · refine ⟨4, ?_⟩
        simp only [eventually_map, eventually_atTop, ge_iff_le]
        exact ⟨0, fun n _ ↦ h_le_4 n r hr⟩
    _ = 2⁻¹ * r * ‖∫ t in -2 * r⁻¹..2 * r⁻¹, 1 - f (t • z)‖ := by
      refine ((Tendsto.norm ?_).const_mul _).limsup_eq
      simp only [neg_mul]
      have hr' : -(2 * r⁻¹) ≤ 2 * r⁻¹ := by rw [neg_le_self_iff]; positivity
      simp_rw [intervalIntegral.integral_of_le hr']
      refine tendsto_integral_of_dominated_convergence (fun _ ↦ 2) ?_ (by fun_prop) ?_ ?_
      · exact fun _ ↦ Measurable.aestronglyMeasurable <| by fun_prop
      · exact fun _ ↦ ae_of_all _ fun _ ↦ norm_one_sub_charFun_le_two
      · exact ae_of_all _ fun x ↦ tendsto_const_nhds.sub (h _)
  -- It suffices to show that the upper bound tends to 0.
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (h := fun r ↦ 2⁻¹ * r * ‖∫ t in -2 * r⁻¹..2 * r⁻¹, 1 - f (t • z)‖) ?_ ?_ ?_
  rotate_left
  · filter_upwards [eventually_gt_atTop 0] with r hr
    refine le_limsup_of_le ?_ fun u hu ↦ ?_
    · refine ⟨4, ?_⟩
      simp only [eventually_map, eventually_atTop, ge_iff_le]
      exact ⟨0, fun n _ ↦ (h_le n r hr).trans (h_le_4 n r hr)⟩
    · exact ENNReal.toReal_nonneg.trans hu.exists.choose_spec
  · filter_upwards [eventually_gt_atTop 0] with r hr using h_limsup_le r hr
  -- We now show that the upper bound tends to 0.
  -- This will follow from the fact that `f` is continuous at `0`.
  -- `⊢ Tendsto (fun r ↦ 2⁻¹ * r * ‖∫ t in -2 * r⁻¹..2 * r⁻¹, 1 - f (t • z)‖) atTop (𝓝 0)`
  have hf_tendsto := hf.tendsto
  rw [Metric.tendsto_nhds_nhds] at hf_tendsto
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hf0 : f 0 = 1 := by symm; simpa using h 0
  simp only [gt_iff_lt, dist_eq_norm_sub', zero_sub, norm_neg, hf0] at hf_tendsto
  simp only [ge_iff_le, neg_mul, dist_zero_right, norm_mul, norm_inv,
    Real.norm_ofNat, Real.norm_eq_abs]
  simp_rw [abs_of_nonneg (norm_nonneg _)]
  obtain ⟨δ, hδ, hδ_lt⟩ : ∃ δ, 0 < δ ∧ ∀ ⦃x : E⦄, ‖x‖ < δ → ‖1 - f x‖ < ε / 4 :=
    hf_tendsto (ε / 4) (by positivity)
  refine ⟨4 * δ⁻¹, fun r hrδ ↦ ?_⟩
  have hr : 0 < r := lt_of_lt_of_le (by positivity) hrδ
  have hr' : -(2 * r⁻¹) ≤ 2 * r⁻¹ := by rw [neg_le_self_iff]; positivity
  have h_le_Ioc x (hx : x ∈ Set.Ioc (-(2 * r⁻¹)) (2 * r⁻¹)) :
      ‖1 - f (x • z)‖ ≤ ε / 4 := by
    refine (hδ_lt ?_).le
    simp only [norm_smul, Real.norm_eq_abs, mul_one, hz]
    calc |x|
    _ ≤ 2 * r⁻¹ := by
      rw [abs_le]
      rw [Set.mem_Ioc] at hx
      exact ⟨hx.1.le, hx.2⟩
    _ < δ := by
      rw [← lt_div_iff₀' (by positivity), inv_lt_comm₀ hr (by positivity)]
      refine lt_of_lt_of_le ?_ hrδ
      ring_nf
      gcongr
      norm_num
  rw [abs_of_nonneg hr.le]
  calc 2⁻¹ * r * ‖∫ t in -(2 * r⁻¹)..2 * r⁻¹, 1 - f (t • z)‖
  _ ≤ 2⁻¹ * r * ∫ t in -(2 * r⁻¹)..2 * r⁻¹, ‖1 - f (t • z)‖ := by
    gcongr
    rw [intervalIntegral.integral_of_le hr', intervalIntegral.integral_of_le hr']
    exact norm_integral_le_integral_norm _
  _ ≤ 2⁻¹ * r * ∫ t in -(2 * r⁻¹)..2 * r⁻¹, ε / 4 := by
    gcongr
    rw [intervalIntegral.integral_of_le hr', intervalIntegral.integral_of_le hr']
    refine integral_mono_ae ?_ (by fun_prop) ?_
    · refine Integrable.mono' (integrable_const (ε / 4)) ?_ ?_
      · exact Measurable.aestronglyMeasurable <| by fun_prop
      · simp_rw [norm_norm]
        exact ae_restrict_of_forall_mem measurableSet_Ioc h_le_Ioc
    · exact ae_restrict_of_forall_mem measurableSet_Ioc h_le_Ioc
  _ = ε / 2 := by
    simp only [intervalIntegral.integral_div, intervalIntegral.integral_const, sub_neg_eq_add,
      smul_eq_mul]
    ring_nf
    rw [mul_inv_cancel₀ hr.ne', one_mul]
  _ < ε := by simp [hε]

end MeasureTheory
