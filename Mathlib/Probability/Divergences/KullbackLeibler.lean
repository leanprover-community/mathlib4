/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Divergences.LogLikelihoodRatio
import Mathlib.Probability.Divergences.FDivergence
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Kullback-Leibler divergence

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

## Notation



## Implementation details



## References

* [F. Bar, *Quuxes*][bibkey]

## Tags

Foobars, barfoos
-/

open Real

open scoped ENNReal NNReal Topology

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α}

section x_log_x

namespace Real

lemma tendsto_log_mul_nhds_zero_left :
    Filter.Tendsto (fun x ↦ log x * x) (𝓝[<] 0) (𝓝 0) := by
  have h := tendsto_log_mul_rpow_nhds_zero zero_lt_one
  simp only [rpow_one] at h
  have h_eq : ∀ x ∈ Set.Iio 0, (- (fun x ↦ log x * x) ∘ (fun x ↦ |x|)) x = log x * x := by
    intro x hx
    simp only [Set.mem_Iio] at hx
    simp only [Pi.neg_apply, Function.comp_apply, log_abs]
    rw [abs_of_nonpos hx.le]
    simp only [mul_neg, neg_neg]
  refine tendsto_nhdsWithin_congr h_eq ?_
  rw [← neg_zero]
  refine Filter.Tendsto.neg ?_
  simp only [neg_zero]
  refine h.comp ?_
  refine tendsto_abs_nhdsWithin_zero.mono_left ?_
  refine nhdsWithin_mono 0 (fun x hx ↦ ?_)
  simp only [Set.mem_Iio] at hx
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff, hx.ne, not_false_eq_true]

lemma continuous_id_mul_log : Continuous (fun x ↦ x * log x) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  swap; · exact (continuous_id'.continuousAt).mul (continuousAt_log hx)
  rw [hx]
  have h := tendsto_log_mul_rpow_nhds_zero zero_lt_one
  simp only [rpow_one] at h
  have h' : Filter.Tendsto (fun x ↦ log x * x) (𝓝[<] 0) (𝓝 0) := tendsto_log_mul_nhds_zero_left
  rw [ContinuousAt, zero_mul]
  suffices Filter.Tendsto (fun x ↦ log x * x) (𝓝 0) (𝓝 0) by
    exact this.congr (fun x ↦ by rw [mul_comm])
  nth_rewrite 1 [← nhdsWithin_univ]
  have : (Set.univ : Set ℝ) = Set.Iio 0 ∪ Set.Ioi 0 ∪ {0} := by
    ext x
    simp only [Set.mem_univ, Set.Iio_union_Ioi, Set.union_singleton, Set.mem_compl_iff,
      Set.mem_singleton_iff, not_true, Set.mem_insert_iff, true_iff]
    exact em _
  rw [this, nhdsWithin_union, nhdsWithin_union]
  simp only [ge_iff_le, nhdsWithin_singleton, sup_le_iff, Filter.nonpos_iff, Filter.tendsto_sup]
  refine ⟨⟨h', h⟩, ?_⟩
  rw [Filter.tendsto_pure_left, mul_zero]
  intro s hs
  obtain ⟨t, hts, _, h_zero_mem⟩ := mem_nhds_iff.mp hs
  exact hts h_zero_mem

lemma differentiableOn_id_mul_log : DifferentiableOn ℝ (fun x ↦ x * log x) {0}ᶜ :=
  differentiable_id'.differentiableOn.mul differentiableOn_log

lemma deriv_id_mul_log {x : ℝ} (hx : x ≠ 0) : deriv (fun x ↦ x * log x) x = log x + 1 := by
  rw [deriv_mul differentiableAt_id' (differentiableAt_log hx)]
  simp only [deriv_id'', one_mul, deriv_log', ne_eq, add_right_inj]
  exact mul_inv_cancel hx

lemma deriv2_id_mul_log {x : ℝ} (hx : x ≠ 0) : deriv^[2] (fun x ↦ x * log x) x = x⁻¹ := by
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp.left_id,
    Function.comp_apply]
  suffices ∀ᶠ y in (𝓝 x), deriv (fun x ↦ x * log x) y = log y + 1 by
    refine (Filter.EventuallyEq.deriv_eq this).trans ?_
    rw [deriv_add_const, deriv_log x]
  suffices ∀ᶠ y in (𝓝 x), y ≠ 0 by
    filter_upwards [this] with y hy
    exact deriv_id_mul_log hy
  exact eventually_ne_nhds hx

lemma strictConvexOn_id_mul_log : StrictConvexOn ℝ (Set.Ici (0 : ℝ)) (fun x ↦ x * log x) := by
  refine strictConvexOn_of_deriv2_pos (convex_Ici 0) (continuous_id_mul_log.continuousOn) ?_
  intro x hx
  simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi] at hx
  rw [deriv2_id_mul_log hx.ne']
  positivity

lemma convexOn_id_mul_log : ConvexOn ℝ (Set.Ici (0 : ℝ)) (fun x ↦ x * log x) :=
  strictConvexOn_id_mul_log.convexOn

lemma id_mul_log_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ x * log x :=
  mul_nonneg (zero_le_one.trans hx) (log_nonneg hx)

@[measurability]
lemma measurable_id_mul_log : Measurable (fun x ↦ x * log x) :=
  measurable_id'.mul measurable_log

end Real

end x_log_x

section llr_and_llrf

lemma integral_llr_eq_integral_lrf {μ ν : Measure α} [SigmaFinite μ]
    [Measure.HaveLebesgueDecomposition μ ν] (hμν : μ ≪ ν) :
    ∫ x, LLR μ ν x ∂μ = ∫ x, LRf (fun x ↦ x * log x) μ ν x ∂ν := by
  simp_rw [LLR, LRf]
  conv_lhs =>
    rw [← Measure.withDensity_rnDeriv_eq _ _ hμν]
    conv in (Measure.rnDeriv (ν.withDensity (μ.rnDeriv ν)) ν) =>
      rw [Measure.withDensity_rnDeriv_eq _ _ hμν]
  have h_rn_eq : μ.rnDeriv ν =ᵐ[ν] fun x ↦ (μ.rnDeriv ν x).toNNReal := by
    filter_upwards [Measure.rnDeriv_lt_top μ ν] with x hx
    rw [ENNReal.coe_toNNReal]
    exact hx.ne
  have h_ν_eq : ν.withDensity (μ.rnDeriv ν)
      = ν.withDensity (fun x ↦ (μ.rnDeriv ν x).toNNReal) := withDensity_congr_ae h_rn_eq
  conv_lhs => rw [h_ν_eq]
  rw [integral_withDensity_eq_integral_smul]
  swap; · exact (Measure.measurable_rnDeriv _ _).ennreal_toNNReal
  congr

end llr_and_llrf

section integral_llr_nonneg

lemma integrable_lrf_mul_log {μ ν : Measure α} [IsFiniteMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) (h_int : Integrable (LLR μ ν) μ) :
    Integrable (LRf (fun x ↦ x * log x) μ ν) ν := by
  simp only [lrf_def]
  exact integrable_rnDeriv_smul hμν h_int

lemma integral_llr_nonneg_aux' {μ ν : Measure α} [IsFiniteMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) (h_int : Integrable (LLR μ ν) μ) :
    (μ Set.univ).toReal * log (μ Set.univ).toReal ≤ ∫ x, LLR μ ν x ∂μ := by
  refine (le_integral_lrf Real.convexOn_id_mul_log Real.continuous_id_mul_log.continuousOn
    (integrable_lrf_mul_log hμν h_int) hμν).trans ?_
  rw [integral_llr_eq_integral_lrf hμν]

lemma integral_llr_ge {μ ν : Measure α} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμν : μ ≪ ν) (h_int : Integrable (LLR μ ν) μ) :
    (μ Set.univ).toReal * log ((μ Set.univ).toReal / (ν Set.univ).toReal) ≤ ∫ x, LLR μ ν x ∂μ := by
  by_cases hμ : μ = 0
  · simp [hμ]
  by_cases hν : ν = 0
  · refine absurd ?_ hμ
    rw [hν] at hμν
    apply? says exact Measure.measure_univ_eq_zero.mp (hμν rfl)
  let ν' := (ν Set.univ)⁻¹ • ν
  have : IsProbabilityMeasure ν' := by
    constructor
    simp only [Measure.smul_toOuterMeasure, OuterMeasure.coe_smul, Pi.smul_apply, smul_eq_mul]
    rw [mul_comm, ENNReal.mul_inv_cancel]
    · simp [hν]
    · exact measure_ne_top _ _
  have h := integral_llr_nonneg_aux' (?_ : μ ≪ ν') ?_
  rotate_left
  · refine Measure.AbsolutelyContinuous.trans hμν ?_
    refine Measure.absolutelyContinuous_of_le_smul (c := ν Set.univ) ?_
    rw [← smul_assoc, smul_eq_mul, ENNReal.mul_inv_cancel, one_smul]
    · simp [hν]
    · exact measure_ne_top _ _
  · rw [integrable_congr (llr_smul_right hμν (ν Set.univ)⁻¹ _ _)]
    rotate_left
    · simp [measure_ne_top ν _]
    · simp [hν]
    exact h_int.sub (integrable_const _)
  rw [integral_congr_ae (llr_smul_right hμν (ν Set.univ)⁻¹ _ _)] at h
  rotate_left
  · simp [measure_ne_top ν _]
  · simp [hν]
  rw [integral_sub h_int (integrable_const _), integral_const, smul_eq_mul, le_sub_iff_add_le,
    ENNReal.toReal_inv, log_inv, mul_neg, ← sub_eq_add_neg] at h
  rwa [log_div, mul_sub]
  · rw [ENNReal.toReal_ne_zero]
    simp [hμ, measure_ne_top μ]
  · rw [ENNReal.toReal_ne_zero]
    simp [hν, measure_ne_top ν]

lemma integral_llr_nonneg {μ ν : Measure α} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) (h_int : Integrable (LLR μ ν) μ) :
    0 ≤ ∫ x, LLR μ ν x ∂μ := by
  rw [integral_llr_eq_integral_lrf hμν]
  exact integral_lrf_nonneg Real.convexOn_id_mul_log Real.continuous_id_mul_log.continuousOn
    (by simp) (integrable_lrf_mul_log hμν h_int) hμν

end integral_llr_nonneg

lemma integral_sub_logIntegralExp_le {μ ν : Measure α}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) (h_int : Integrable (LLR μ ν) μ)
    (f : α → ℝ) (hfμ : Integrable f μ) (hf : Integrable (fun x ↦ exp (f x)) ν) :
    ∫ x, f x ∂μ - log (∫ x, exp (f x) ∂ν) ≤ ∫ x, LLR μ ν x ∂μ := by
  have : ∫ x, LLR μ ν x ∂μ - ∫ x, LLR μ (ν.tilted f) x ∂μ
      = ∫ x, f x ∂μ - log (∫ x, exp (f x) ∂ν) := by
    rw [integral_llr_tilted_right hμν hfμ hf h_int]
    abel
  rw [← this]
  simp only [tsub_le_iff_right, le_add_iff_nonneg_right]
  have : IsProbabilityMeasure (Measure.tilted ν f) := isProbabilityMeasure_tilted hf
  refine integral_llr_nonneg (hμν.trans (absolutelyContinuous_tilted hf)) ?_
  exact integrable_llr_tilted_right hμν hfμ hf h_int

lemma ciSup_le_integral_llr {μ ν : Measure α} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) (h_int : Integrable (LLR μ ν) μ) :
    ⨆ (f : α → ℝ) (_ : Integrable f μ)
        (_ : Integrable (fun x ↦ exp (f x)) ν), ∫ x, f x ∂μ - log (∫ x, exp (f x) ∂ν)
      ≤ ∫ x, LLR μ ν x ∂μ := by
  refine ciSup_le (fun f ↦ ?_)
  by_cases hfμ : Integrable f μ
  · simp only [hfμ, ciSup_unique]
    by_cases hf : Integrable (fun x ↦ exp (f x)) ν
    · simp only [hf, ciSup_unique]
      exact integral_sub_logIntegralExp_le hμν h_int f hfμ hf
    · simp [hf, ciSup_empty]
      exact integral_llr_nonneg hμν h_int
  · simp only [hfμ, ciSup_empty]
    exact integral_llr_nonneg hμν h_int

/-- Logarithm of the sum of the likelihood ratio and a constant `u`.
This is used with `0 < u` to avoid issues with `LLR` due to the likelihood ratio being 0. -/
noncomputable
def LLRAddConst (μ ν : Measure α) (u : ℝ) (x : α) : ℝ := log ((μ.rnDeriv ν x).toReal + u)

@[simp]
lemma llrAddConst_zero (μ ν : Measure α) : LLRAddConst μ ν 0 = LLR μ ν := by
  ext x
  rw [LLRAddConst, LLR, add_zero]

lemma exp_llrAddConst {μ ν : Measure α} {u : ℝ} (hu : 0 < u) (x : α) :
    exp (LLRAddConst μ ν u x) = (μ.rnDeriv ν x).toReal + u := by
  rw [LLRAddConst, exp_log]
  positivity

lemma measurable_llrAddConst {μ ν : Measure α} {u : ℝ} :
    Measurable (LLRAddConst μ ν u) :=
  ((Measure.measurable_rnDeriv μ ν).ennreal_toReal.add measurable_const).log

lemma stronglyMeasurable_llrAddConst {μ ν : Measure α} {u : ℝ} :
    StronglyMeasurable (LLRAddConst μ ν u) :=
  measurable_llrAddConst.stronglyMeasurable

lemma log_le_llrAddConst {μ ν : Measure α} {u : ℝ} {x : α} (hu : 0 < u) :
    log u ≤ LLRAddConst μ ν u x := by
  rw [LLRAddConst, Real.log_le_log_iff hu]
  · simp
  · positivity

lemma llrAddConst_le_log_max {μ ν : Measure α} {u : ℝ} {x : α} (hu : 0 < u) :
    LLRAddConst μ ν u x ≤ log (max (μ.rnDeriv ν x).toReal u) + log 2 := by
  rw [← log_mul _ two_ne_zero]
  swap; · refine ne_of_gt ?_; positivity
  rw [LLRAddConst, Real.log_le_log_iff]
  · rw [mul_two]
    exact add_le_add (le_max_left _ _) (le_max_right _ _)
  · positivity
  · positivity

lemma abs_llrAddConst_le {μ ν : Measure α} {u : ℝ} {x : α} (hu : 0 < u) :
    |LLRAddConst μ ν u x| ≤ |log (μ.rnDeriv ν x).toReal| + |log u| + log 2 := by
  cases' le_or_lt 0 (LLRAddConst μ ν u x) with h h
  · rw [abs_of_nonneg h]
    refine (llrAddConst_le_log_max hu).trans (add_le_add ?_ le_rfl)
    cases' le_or_lt (μ.rnDeriv ν x).toReal u with h' h'
    · rw [max_eq_right h', add_comm]
      exact le_add_of_le_of_nonneg (le_abs_self _) (abs_nonneg _)
    · rw [max_eq_left h'.le]
      exact le_add_of_le_of_nonneg (le_abs_self _) (abs_nonneg _)
  · rw [abs_of_nonpos h.le]
    calc - LLRAddConst μ ν u x
      ≤ - log u := neg_le_neg (log_le_llrAddConst hu)
    _ ≤ |log u| := neg_le_abs_self _
    _ ≤ |log u| + |log (ENNReal.toReal (Measure.rnDeriv μ ν x))| + log 2 := by
          rw [add_assoc]
          exact le_add_of_le_of_nonneg le_rfl (by positivity)
    _ = |log (ENNReal.toReal (Measure.rnDeriv μ ν x))| + |log u| + log 2 := by abel

lemma integrable_llrAddConst {μ ν : Measure α} [IsFiniteMeasure μ] {u : ℝ} (hu : 0 ≤ u)
    (h_int : Integrable (LLR μ ν) μ) :
    Integrable (LLRAddConst μ ν u) μ := by
  cases' eq_or_lt_of_le hu with hu hu
  · simp [hu.symm, h_int]
  have h_le : ∀ x, ‖LLRAddConst μ ν u x‖ ≤ ‖|log (μ.rnDeriv ν x).toReal| + |log u| + log 2‖ := by
    simp only [norm_eq_abs]
    intro x
    have h : 0 ≤ |log (ENNReal.toReal (Measure.rnDeriv μ ν x))| + |log u| + log 2 := by positivity
    rw [abs_of_nonneg h]
    exact abs_llrAddConst_le hu
  refine Integrable.mono ?_ stronglyMeasurable_llrAddConst.aestronglyMeasurable (ae_of_all _ h_le)
  exact (h_int.abs.add (integrable_const _)).add (integrable_const _)

lemma integrable_exp_llrAddConst {μ ν : Measure α} [IsFiniteMeasure μ] [IsFiniteMeasure ν] {u : ℝ}
    (hu : 0 < u) :
    Integrable (fun x ↦ exp (LLRAddConst μ ν u x)) ν := by
  simp_rw [exp_llrAddConst hu]
  exact Measure.integrable_toReal_rnDeriv.add (integrable_const _)

lemma logIntegralExp_llrAddConst {μ ν : Measure α} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) {u : ℝ} (hu : 0 < u) :
    log (∫ x, exp (LLRAddConst μ ν u x) ∂ν) = log (1 + u) := by
  simp_rw [exp_llrAddConst hu]
  rw [integral_add Measure.integrable_toReal_rnDeriv (integrable_const _), integral_const]
  simp only [measure_univ, ENNReal.one_toReal, smul_eq_mul, one_mul]
  congr
  rw [Measure.integral_toReal_rnDeriv hμν]
  simp only [measure_univ, ENNReal.one_toReal]

lemma integral_llr_le_integral_llrAddConst {μ ν : Measure α} [IsFiniteMeasure μ]
    [Measure.HaveLebesgueDecomposition μ ν] {u : ℝ}
    (hu : 0 ≤ u) (hμν : μ ≪ ν) (h_int : Integrable (LLR μ ν) μ) :
    ∫ x, LLR μ ν x ∂μ ≤ ∫ x, LLRAddConst μ ν u x ∂μ := by
  refine integral_mono_ae h_int (integrable_llrAddConst hu h_int) ?_
  filter_upwards [Measure.rnDeriv_pos hμν, hμν.ae_le (Measure.rnDeriv_lt_top μ ν)]
    with x hx_pos hx_lt_top
  rw [LLR, LLRAddConst, Real.log_le_log_iff]
  · exact le_add_of_le_of_nonneg le_rfl hu
  · exact ENNReal.toReal_pos hx_pos.ne' hx_lt_top.ne
  · exact add_pos_of_pos_of_nonneg (ENNReal.toReal_pos hx_pos.ne' hx_lt_top.ne) hu

lemma integral_llr_le_ciInf_integral_llrAddConst {μ ν : Measure α}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμν : μ ≪ ν) (h_int : Integrable (LLR μ ν) μ) :
    ∫ x, LLR μ ν x ∂μ ≤ ⨅ u : {v // (0 : ℝ) < v}, ∫ x, LLRAddConst μ ν u x ∂μ :=
  le_ciInf (fun u ↦ integral_llr_le_integral_llrAddConst u.2.le hμν h_int)

lemma integral_llrAddConst_le_ciSup_add {μ ν : Measure α}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) (h_int : Integrable (LLR μ ν) μ) {u : ℝ} (hu : 0 < u) :
    ∫ x, LLRAddConst μ ν u x ∂μ ≤ (⨆ u' : {v // (0 : ℝ) < v},
      ∫ x, LLRAddConst μ ν u' x ∂μ - log (∫ x, exp (LLRAddConst μ ν u' x) ∂ν)) + log (1 + u) := by
    calc ∫ x, LLRAddConst μ ν u x ∂μ
      = ∫ x, LLRAddConst μ ν u x ∂μ - log (∫ x, exp (LLRAddConst μ ν u x) ∂ν)
        + log (∫ x, exp (LLRAddConst μ ν u x) ∂ν) := by abel
    _ ≤ (⨆ u : {v // (0 : ℝ) < v},
          ∫ x, LLRAddConst μ ν u x ∂μ - log (∫ x, exp (LLRAddConst μ ν u x) ∂ν))
        + log (∫ x, exp (LLRAddConst μ ν u x) ∂ν) := by
          refine add_le_add ?_ le_rfl
          refine le_ciSup_of_le ?_ ⟨u, hu⟩ le_rfl
          refine ⟨∫ x, LLR μ ν x ∂μ, fun y ⟨u, huy⟩ ↦ ?_⟩
          rw [← huy]
          exact integral_sub_logIntegralExp_le hμν h_int (LLRAddConst μ ν _)
            (integrable_llrAddConst u.2.le h_int) (integrable_exp_llrAddConst u.2)
    _ = (⨆ u : {v // (0 : ℝ) < v},
          ∫ x, LLRAddConst μ ν u x ∂μ - log (∫ x, exp (LLRAddConst μ ν u x) ∂ν))
        + log (1 + u) := by rw [logIntegralExp_llrAddConst hμν hu]

lemma integral_llr_le_ciSup_integral_llrAddConst_sub {μ ν : Measure α}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) (h_int : Integrable (LLR μ ν) μ) :
    ∫ x, LLR μ ν x ∂μ ≤ ⨆ u : {v // (0 : ℝ) < v},
      ∫ x, LLRAddConst μ ν u x ∂μ - log (∫ x, exp (LLRAddConst μ ν u x) ∂ν) := by
    have h_bdd : BddBelow (Set.range fun u : {v // (0 : ℝ) < v} ↦ log (1 + u)) := by
      refine ⟨0, fun y ⟨u, huy⟩ ↦ ?_⟩
      rw [← huy]
      refine log_nonneg ?_
      simp [u.2.le]
    calc ∫ x, LLR μ ν x ∂μ
      ≤ ⨅ u : {v // (0 : ℝ) < v}, ∫ x, LLRAddConst μ ν u x ∂μ :=
          integral_llr_le_ciInf_integral_llrAddConst hμν h_int
    _ ≤ ⨅ u : {v // (0 : ℝ) < v}, (⨆ u' : {v // (0 : ℝ) < v},
        ∫ x, LLRAddConst μ ν u' x ∂μ - log (∫ x, exp (LLRAddConst μ ν u' x) ∂ν)) + log (1 + u) := by
          refine ciInf_mono ?_ ?_
          · refine ⟨∫ x, LLR μ ν x ∂μ, fun y ⟨u, huy⟩ ↦ ?_⟩
            rw [← huy]
            exact integral_llr_le_integral_llrAddConst u.2.le hμν h_int
          · exact fun u ↦ integral_llrAddConst_le_ciSup_add hμν h_int u.2
    _ = (⨆ u' : {v // (0 : ℝ) < v},
          ∫ x, LLRAddConst μ ν u' x ∂μ - log (∫ x, exp (LLRAddConst μ ν u' x) ∂ν))
        + ⨅ u : {v // (0 : ℝ) < v}, log (1 + u) := by
          rw [← add_ciInf h_bdd]
    _ = ⨆ u : {v // (0 : ℝ) < v},
        ∫ x, LLRAddConst μ ν u x ∂μ - log (∫ x, exp (LLRAddConst μ ν u x) ∂ν) := by
          suffices ⨅ (u : {v // (0 : ℝ) < v}), log (1 + u) = 0 by
            rw [this, add_zero]
          apply le_antisymm
          · refine le_of_forall_pos_le_add (fun ε hε ↦ ?_)
            exact ciInf_le_of_le h_bdd ⟨exp ε - 1, by simp [hε]⟩ (by simp)
          · refine le_ciInf (fun u ↦ log_nonneg ?_)
            simp [u.2.le]

lemma integral_llr_le_ciSup {μ ν : Measure α} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) (h_int : Integrable (LLR μ ν) μ) :
    ∫ x, LLR μ ν x ∂μ
      ≤ ⨆ (f : α → ℝ) (_ : Integrable f μ) (_ : Integrable (fun x ↦ exp (f x)) ν),
        ∫ x, f x ∂μ - log (∫ x, exp (f x) ∂ν) := by
  refine (integral_llr_le_ciSup_integral_llrAddConst_sub hμν h_int).trans ?_
  refine ciSup_le (fun u ↦ ?_)
  refine le_ciSup_of_le ?_ (LLRAddConst μ ν u) ?_
  · refine ⟨∫ x, LLR μ ν x ∂μ, fun x ⟨f, hf⟩ ↦ ?_⟩
    rw [← hf]
    by_cases hfμ : Integrable f μ
    · simp only [hfμ, ciSup_unique]
      by_cases hf : Integrable (fun x ↦ exp (f x)) ν
      · simp only [hf, ciSup_unique]
        exact integral_sub_logIntegralExp_le hμν h_int f hfμ hf
      · simp only [hf, ciSup_empty]
        exact integral_llr_nonneg hμν h_int
    · simp only [hfμ, ciSup_empty]
      exact integral_llr_nonneg hμν h_int
  · simp [integrable_llrAddConst u.2.le h_int, integrable_exp_llrAddConst u.2]

/-- **Donsker-Varadhan** variational formula for the Kullback-Leibler divergence. -/
theorem DonskerVaradhan {μ ν : Measure α} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) (h_int : Integrable (LLR μ ν) μ) :
    ∫ x, LLR μ ν x ∂μ
      = ⨆ (f : α → ℝ) (_ : Integrable f μ) (_ : Integrable (fun x ↦ exp (f x)) ν),
        ∫ x, f x ∂μ - log (∫ x, exp (f x) ∂ν) :=
  le_antisymm (integral_llr_le_ciSup hμν h_int) (ciSup_le_integral_llr hμν h_int)

-- TODO: this should be in EReal?
/-- Kullback-Leibler divergence. -/
noncomputable
def KL (μ ν : Measure α) [Decidable (μ ≪ ν)] [Decidable (Integrable (LLR μ ν) μ)] : ℝ≥0∞ :=
  if μ ≪ ν ∧ Integrable (LLR μ ν) μ then ENNReal.ofReal (∫ x, LLR μ ν x ∂μ) else ∞

end MeasureTheory
