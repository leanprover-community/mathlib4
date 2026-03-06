/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Measure.IntegralCharFun
public import Mathlib.MeasureTheory.Measure.TightNormed

import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Prokhorov

/-!
# Lévy's convergence theorem

This file contains developments retaled to Lévy's convergence theorem, which links convergence of
characteristic functions and convergence in distribution in finite dimensional inner product spaces.

## Main statements

* `isTightMeasureSet_of_tendsto_charFun`: if the characteristic functions of a sequence of measures
  `μ : ℕ → Measure E` on a finite dimensional inner product space converge pointwise
  to a function which is continuous at 0, then `{μ n | n}` is tight.
* `ProbabilityMeasure.tendsto_iff_tendsto_charFun`: the weak convergence of probability measures is
  equivalent to the pointwise convergence of their characteristic functions.

-/

public section

open Filter BoundedContinuousFunction Real RCLike
open scoped Topology RealInnerProductSpace ENNReal

namespace MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- If the characteristic functions of a sequence of measures `μ : ℕ → Measure E` converge pointwise
to a function which is continuous at 0, then `{μ n | n}` is tight. -/
lemma isTightMeasureSet_of_tendsto_charFun {μ : ℕ → Measure E} [∀ i, IsProbabilityMeasure (μ i)]
    {f : E → ℂ} (hf : ContinuousAt f 0)
    (h : ∀ t, Tendsto (fun n ↦ charFun (μ n) t) atTop (𝓝 (f t))) :
    IsTightMeasureSet (Set.range μ) := by
  -- it suffices to show that a limsup tends to 0
  refine isTightMeasureSet_range_of_tendsto_limsup_measureReal_inner_of_norm_eq_one ℝ
    (fun z hz ↦ ?_) 1 (.of_forall fun _ ↦ by simp)
  -- first, prove an auxiliary inequality that will be used to bound the limsup
  have h_le_4 n r (hr : 0 < r) :
      2⁻¹ * r * ‖∫ t in -2 * r⁻¹..2 * r⁻¹, 1 - charFun (μ n) (t • z)‖ ≤ 4 := by
    have hr' : -(2 * r⁻¹) ≤ 2 * r⁻¹ := by rw [neg_le_self_iff]; positivity
    calc 2⁻¹ * r * ‖∫ t in -2 * r⁻¹..2 * r⁻¹, 1 - charFun (μ n) (t • z)‖
    _ ≤ 2⁻¹ * r * ∫ t in -(2 * r⁻¹)..2 * r⁻¹, ‖1 - charFun (μ n) (t • z)‖ := by
      grw [neg_mul, intervalIntegral.norm_integral_le_integral_norm hr']
    _ ≤ 2⁻¹ * r * ∫ t in -(2 * r⁻¹)..2 * r⁻¹, 2 := by
      gcongr
      rw [intervalIntegral.integral_of_le hr', intervalIntegral.integral_of_le hr']
      refine integral_mono_of_nonneg ?_ (by fun_prop) ?_
      · exact ae_of_all _ fun _ ↦ by positivity
      · exact ae_of_all _ fun _ ↦ norm_one_sub_charFun_le_two
    _ ≤ 4 := by
      simp only [intervalIntegral.integral_const, sub_neg_eq_add, smul_eq_mul]
      field_simp
      norm_num
  have h_le n r (hr : 0 < r) : (μ n).real {x | r < |⟪z, x⟫|} ≤
      2⁻¹ * r * ‖∫ t in -2 * r⁻¹..2 * r⁻¹, 1 - charFun (μ n) (t • z)‖ :=
    measureReal_abs_inner_gt_le_integral_charFun hr
  -- We introduce an upper bound for the limsup.
  -- This is where we use that `charFun (μ n)` converges to `f`.
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
      · exact ae_of_all _ fun _ ↦ tendsto_const_nhds.sub (h _)
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
    Real.norm_ofNat, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  obtain ⟨δ, hδ, hδ_lt⟩ : ∃ δ, 0 < δ ∧ ∀ ⦃x : E⦄, ‖x‖ < δ → ‖1 - f x‖ < ε / 4 :=
    hf_tendsto (ε / 4) (by positivity)
  refine ⟨4 * δ⁻¹, fun r hrδ ↦ ?_⟩
  have hr : 0 < r := lt_of_lt_of_le (by positivity) hrδ
  have hr' : -(2 * r⁻¹) ≤ 2 * r⁻¹ := by rw [neg_le_self_iff]; positivity
  have h_le_Ioc x (hx : x ∈ Set.Ioc (-(2 * r⁻¹)) (2 * r⁻¹)) : ‖1 - f (x • z)‖ ≤ ε / 4 := by
    refine (hδ_lt ?_).le
    simp only [norm_smul, Real.norm_eq_abs, mul_one, hz]
    calc |x|
    _ ≤ 2 * r⁻¹ := by simp at hx; grind
    _ < δ := by
      rw [← lt_div_iff₀' (by positivity), inv_lt_comm₀ hr (by positivity)]
      refine lt_of_lt_of_le ?_ hrδ
      field_simp
      norm_num
  rw [abs_of_nonneg hr.le]
  calc 2⁻¹ * r * ‖∫ t in -(2 * r⁻¹)..2 * r⁻¹, 1 - f (t • z)‖
  _ ≤ 2⁻¹ * r * ∫ t in -(2 * r⁻¹)..2 * r⁻¹, ‖1 - f (t • z)‖ := by
    grw [intervalIntegral.norm_integral_le_integral_norm hr']
  _ ≤ 2⁻¹ * r * ∫ t in -(2 * r⁻¹)..2 * r⁻¹, ε / 4 := by
    gcongr
    rw [intervalIntegral.integral_of_le hr', intervalIntegral.integral_of_le hr']
    have hf_meas : Measurable f := by
      refine measurable_of_tendsto_metrizable (f := fun n t ↦ charFun (μ n) t) (by fun_prop) ?_
      rwa [tendsto_pi_nhds]
    refine integral_mono_ae ?_ (by fun_prop) ?_
    · refine Integrable.mono' (integrable_const (ε / 4)) ?_ ?_
      · exact Measurable.aestronglyMeasurable <| by fun_prop
      · simpa using ae_restrict_of_forall_mem measurableSet_Ioc h_le_Ioc
    · exact ae_restrict_of_forall_mem measurableSet_Ioc h_le_Ioc
  _ = ε / 2 := by simp; field
  _ < ε := by simp [hε]

/-- Let `μ` be a tight sequence of probability measures and `μ₀` a probability measure.
If `A` is a star sub-algebra of bounded continuous scalar functions that separates points
and the integrals of elements of `A` with respect to `μ` converge to the integrals
with respect to `μ₀`, then `μ` converges weakly to `μ₀`. -/
lemma ProbabilityMeasure.tendsto_of_tight_of_separatesPoints (𝕜 : Type*) [RCLike 𝕜]
    {E : Type*} [MetricSpace E] [CompleteSpace E] [SecondCountableTopology E]
    [MeasurableSpace E] [BorelSpace E] {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {μ : ι → ProbabilityMeasure E} (h_tight : IsTightMeasureSet {(μ n : Measure E) | n})
    {μ₀ : ProbabilityMeasure E}
    {A : StarSubalgebra 𝕜 (E →ᵇ 𝕜)} (hA : (A.map (toContinuousMapStarₐ 𝕜)).SeparatesPoints)
    (heq : ∀ g ∈ A, Tendsto (fun n ↦ ∫ x, g x ∂(μ n)) l (𝓝 (∫ x, g x ∂μ₀))) :
    Tendsto μ l (𝓝 μ₀) := by
  refine Filter.tendsto_of_subseq_tendsto fun ns hns ↦ ?_
  have h_compact : IsCompact (closure {μ n | n}) :=
    isCompact_closure_of_isTightMeasureSet (S := {μ n | n}) (by simpa using h_tight)
  obtain ⟨μ', hμ'_mem, φ, hφ_mono, hφ_tendsto⟩ : ∃ μ' ∈ closure {μ n | n},
      ∃ φ, StrictMono φ ∧ Tendsto ((fun n ↦ μ (ns n)) ∘ φ) atTop (𝓝 μ') :=
    h_compact.tendsto_subseq fun n ↦ subset_closure ⟨ns n, rfl⟩
  refine ⟨φ, ?_⟩
  suffices μ' = μ₀ from this ▸ hφ_tendsto
  suffices (μ' : Measure E) = μ₀ by ext; rw [this]
  refine ext_of_forall_mem_subalgebra_integral_eq_of_pseudoEMetric_complete_countable hA
    fun g hg ↦ ?_
  specialize heq g hg
  suffices Tendsto (fun n ↦ ∫ x, g x ∂(μ (ns (φ n)))) atTop (𝓝 (∫ x, g x ∂μ')) from
    tendsto_nhds_unique this <| heq.comp (hns.comp hφ_mono.tendsto_atTop)
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto 𝕜] at hφ_tendsto
  exact hφ_tendsto g

variable {ι : Type*} {l : Filter ι} {μ₀ : ProbabilityMeasure E}

set_option backward.isDefEq.respectTransparency false
omit [FiniteDimensional ℝ E] in
lemma ProbabilityMeasure.tendsto_charPoly_of_tendsto_charFun {μ : ι → ProbabilityMeasure E}
    (h : ∀ t : E, Tendsto (fun n ↦ charFun (μ n) t) l (𝓝 (charFun μ₀ t)))
    {g : E →ᵇ ℂ} (hg : g ∈ charPoly continuous_probChar (L := innerₗ E) continuous_inner) :
    Tendsto (fun n ↦ ∫ x, g x ∂(μ n)) l (𝓝 (∫ x, g x ∂μ₀)) := by
  rw [mem_charPoly] at hg
  obtain ⟨w, hw⟩ := hg
  have h_eq (μ : Measure E) (hμ : IsProbabilityMeasure μ) :
      ∫ x, g x ∂μ = ∑ a ∈ w.support, w a * ∫ x, (probChar (innerₗ E x a) : ℂ) ∂μ := by
    simp_rw [hw]
    rw [integral_finset_sum]
    · congr with y
      rw [integral_const_mul]
    · refine fun i hi ↦ Integrable.const_mul ?_ _
      change Integrable (innerProbChar i) μ
      exact BoundedContinuousFunction.integrable μ _
  simp_rw [h_eq (μ _), h_eq μ₀]
  refine tendsto_finset_sum _ fun y hy ↦ Tendsto.const_mul _ ?_
  simpa [← charFun_eq_integral_probChar] using h y

variable {μ : ℕ → ProbabilityMeasure E}

/-- If the characteristic functions of a sequence of probability measures converge pointwise to
the characteristic function of a probability measure, then the measures converge weakly. -/
lemma ProbabilityMeasure.tendsto_of_tendsto_charFun
    (h : ∀ t : E, Tendsto (fun n ↦ charFun (μ n) t) atTop (𝓝 (charFun μ₀ t))) :
    Tendsto μ atTop (𝓝 μ₀) := by
  have h_tight : IsTightMeasureSet (𝓧 := E) {μ n | n} :=
    isTightMeasureSet_of_tendsto_charFun (by fun_prop) h
  refine tendsto_of_tight_of_separatesPoints h_tight (𝕜 := ℂ)
    (A := charPoly continuous_probChar (L := innerₗ E) continuous_inner) ?_ ?_
  · refine separatesPoints_charPoly continuous_probChar probChar_ne_one _ ?_
    exact fun v hv ↦ DFunLike.ne_iff.mpr ⟨v, inner_self_ne_zero.mpr hv⟩
  · exact fun g ↦ tendsto_charPoly_of_tendsto_charFun h

/-- The **Lévy convergence theorem**: the weak convergence of probability measures is equivalent
to the pointwise convergence of their characteristic functions. -/
theorem ProbabilityMeasure.tendsto_iff_tendsto_charFun :
    Tendsto μ atTop (𝓝 μ₀) ↔
      ∀ t : E, Tendsto (fun n ↦ charFun (μ n) t) atTop (𝓝 (charFun μ₀ t)) := by
  refine ⟨fun h t ↦ ?_, tendsto_of_tendsto_charFun⟩
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ] at h
  simp_rw [charFun_eq_integral_innerProbChar]
  exact h (innerProbChar t)

end MeasureTheory
