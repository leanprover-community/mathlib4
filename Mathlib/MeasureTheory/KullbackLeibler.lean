/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Calculus.MeanValue
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

open scoped ENNReal NNReal

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α}

section Right -- todo: move to that section of Algebra/Bounds.lean

variable {ι G : Type*} [Group G] [ConditionallyCompleteLattice G]
  [CovariantClass G G (Function.swap (· * ·)) (· ≤ ·)] [Nonempty ι] {f : ι → G}

@[to_additive]
theorem ciInf_mul (hf : BddBelow (Set.range f)) (a : G) : (⨅ i, f i) * a = ⨅ i, f i * a :=
  (OrderIso.mulRight a).map_ciInf hf

@[to_additive]
theorem ciInf_div (hf : BddBelow (Set.range f)) (a : G) : (⨅ i, f i) / a = ⨅ i, f i / a := by
  simp only [div_eq_mul_inv, ciInf_mul hf]

end Right

section Left

variable {ι G : Type*} [Group G] [ConditionallyCompleteLattice G]
  [CovariantClass G G (· * ·) (· ≤ ·)] [Nonempty ι] {f : ι → G}

@[to_additive]
theorem mul_ciInf (hf : BddBelow (Set.range f)) (a : G) : (a * ⨅ i, f i) = ⨅ i, a * f i :=
  (OrderIso.mulLeft a).map_ciInf hf

end Left

section x_log_x

namespace Real

lemma continuous_id_mul_log : Continuous (fun x ↦ x * log x) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  swap; · exact (continuous_id'.continuousAt).mul (continuousAt_log hx)
  rw [hx]
  sorry

lemma differentiableOn_id_mul_log : DifferentiableOn ℝ (fun x ↦ x * log x) {0}ᶜ :=
  differentiable_id'.differentiableOn.mul differentiableOn_log

lemma deriv_id_mul_log {x : ℝ} (hx : x ≠ 0) : deriv (fun x ↦ x * log x) x = log x + 1 := by
  rw [deriv_mul differentiableAt_id' (differentiableAt_log hx)]
  simp only [deriv_id'', one_mul, deriv_log', ne_eq, add_right_inj]
  exact mul_inv_cancel hx

lemma deriv2_id_mul_log {x : ℝ} (hx : x ≠ 0) : deriv^[2] (fun x ↦ x * log x) x = x⁻¹ := by
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp.left_id,
    Function.comp_apply]
  sorry

lemma convexOn_id_mul_log : ConvexOn ℝ (Set.Ici (0 : ℝ)) (fun x ↦ x * log x) := by
  have h_ss : interior (Set.Ici (0 : ℝ)) ⊆ {0}ᶜ := by
    intro x
    simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi, Set.mem_compl_iff,
      Set.mem_singleton_iff]
    exact fun hx_pos ↦ hx_pos.ne'
  refine convexOn_of_deriv2_nonneg ?_ ?_ ?_ ?_ ?_
  · exact convex_Ici 0
  · exact continuous_id_mul_log.continuousOn
  · refine differentiableOn_id_mul_log.mono h_ss
  · refine DifferentiableOn.congr_mono ?_ (?_ : ∀ x ∈ interior (Set.Ici (0 : ℝ)), _ = log x + 1)
      h_ss
    · exact DifferentiableOn.add_const differentiableOn_log 1
    · intro x hx
      simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi] at hx
      exact deriv_id_mul_log hx.ne'
  · intro x hx
    simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi] at hx
    rw [deriv2_id_mul_log hx.ne']
    positivity

lemma id_mul_log_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ x * log x :=
  mul_nonneg (zero_le_one.trans hx) (log_nonneg hx)

@[measurability]
lemma measurable_id_mul_log : Measurable (fun x ↦ x * log x) :=
  measurable_id'.mul measurable_log

end Real

end x_log_x

section LLR

@[measurability]
lemma measurable_toReal_rnDeriv (μ ν : Measure α) : Measurable (fun x ↦ (μ.rnDeriv ν x).toReal) :=
  (Measure.measurable_rnDeriv μ ν).ennreal_toReal

lemma stronglyMeasurable_toReal_rnDeriv (μ ν : Measure α) :
    StronglyMeasurable (fun x ↦ (μ.rnDeriv ν x).toReal) :=
  (measurable_toReal_rnDeriv μ ν).stronglyMeasurable

/-- Log-Likelihood Ratio. -/
noncomputable
def LLR (μ ν : Measure α) (x : α) : ℝ := log (μ.rnDeriv ν x).toReal

lemma llr_def (μ ν : Measure α) : LLR μ ν = fun x ↦ log (μ.rnDeriv ν x).toReal := rfl

lemma exp_llr (μ ν : Measure α) [SigmaFinite μ] :
    (fun x ↦ exp (LLR μ ν x))
      =ᵐ[ν] fun x ↦ if μ.rnDeriv ν x = 0 then 1 else (μ.rnDeriv ν x).toReal := by
  filter_upwards [Measure.rnDeriv_lt_top μ ν] with x hx
  by_cases h_zero : μ.rnDeriv ν x = 0
  · simp only [LLR, h_zero, ENNReal.zero_toReal, log_zero, exp_zero, ite_true]
  rw [LLR, exp_log, if_neg h_zero]
  rw [ENNReal.toReal_pos_iff]
  exact ⟨lt_of_le_of_ne (zero_le _) (Ne.symm h_zero), hx⟩

lemma exp_llr_of_ac (μ ν : Measure α) [SigmaFinite μ] [Measure.HaveLebesgueDecomposition μ ν]
    (hμν : μ ≪ ν) :
    (fun x ↦ exp (LLR μ ν x)) =ᵐ[μ] fun x ↦ (μ.rnDeriv ν x).toReal := by
  filter_upwards [hμν.ae_le (exp_llr μ ν), Measure.rnDeriv_pos hμν] with x hx_eq hx_pos
  rw [hx_eq, if_neg hx_pos.ne']

@[measurability]
lemma measurable_llr (μ ν : Measure α) : Measurable (LLR μ ν) :=
  (measurable_toReal_rnDeriv μ ν).log

@[measurability]
lemma stronglyMeasurable_llr (μ ν : Measure α) : StronglyMeasurable (LLR μ ν) :=
  (measurable_llr μ ν).stronglyMeasurable

lemma llr_smul_left {μ ν : Measure α} [IsFiniteMeasure μ] [Measure.HaveLebesgueDecomposition μ ν]
    (hμν : μ ≪ ν) (c : ℝ≥0∞) (hc : c ≠ 0) (hc_ne_top : c ≠ ∞) :
    LLR (c • μ) ν =ᵐ[μ] fun x ↦ LLR μ ν x + log c.toReal := by
  simp only [LLR, llr_def]
  have h := Measure.rnDeriv_smul_left_of_ne_top μ ν hc_ne_top
  filter_upwards [hμν.ae_le h, Measure.rnDeriv_pos hμν, hμν.ae_le (Measure.rnDeriv_lt_top μ ν)]
    with x hx_eq hx_pos hx_ne_top
  rw [hx_eq]
  simp only [Pi.smul_apply, smul_eq_mul, ENNReal.toReal_mul]
  rw [log_mul]
  rotate_left
  · rw [ENNReal.toReal_ne_zero]
    simp [hc, hc_ne_top]
  · rw [ENNReal.toReal_ne_zero]
    simp [hx_pos.ne', hx_ne_top.ne]
  ring

lemma llr_smul_right {μ ν : Measure α} [IsFiniteMeasure μ] [Measure.HaveLebesgueDecomposition μ ν]
    (hμν : μ ≪ ν) (c : ℝ≥0∞) (hc : c ≠ 0) (hc_ne_top : c ≠ ∞) :
    LLR μ (c • ν) =ᵐ[μ] fun x ↦ LLR μ ν x - log c.toReal := by
  simp only [LLR, llr_def]
  have h := Measure.rnDeriv_smul_right_of_ne_top μ ν hc hc_ne_top
  filter_upwards [hμν.ae_le h, Measure.rnDeriv_pos hμν, hμν.ae_le (Measure.rnDeriv_lt_top μ ν)]
    with x hx_eq hx_pos hx_ne_top
  rw [hx_eq]
  simp only [Pi.smul_apply, smul_eq_mul, ENNReal.toReal_mul]
  rw [log_mul]
  rotate_left
  · rw [ENNReal.toReal_ne_zero]
    simp [hc, hc_ne_top]
  · rw [ENNReal.toReal_ne_zero]
    simp [hx_pos.ne', hx_ne_top.ne]
  rw [ENNReal.toReal_inv, log_inv]
  ring

end LLR

section integral_llr_nonneg

lemma integrable_toReal_rnDeriv_mul {μ ν : Measure α} {f : α → ℝ} [SigmaFinite μ]
    [Measure.HaveLebesgueDecomposition μ ν]
    (hμν : μ ≪ ν) (h_int : Integrable f μ) (hf : AEStronglyMeasurable f ν) :
    Integrable (fun x ↦ (Measure.rnDeriv μ ν x).toReal * f x) ν := by
  rw [← memℒp_one_iff_integrable]
  refine ⟨(stronglyMeasurable_toReal_rnDeriv μ ν).aestronglyMeasurable.mul hf, ?_⟩
  simp only [snorm_one_eq_lintegral_nnnorm, nnnorm_mul, ENNReal.coe_mul]
  simp_rw [← ofReal_norm_eq_coe_nnnorm, norm_of_nonneg ENNReal.toReal_nonneg,
    ofReal_norm_eq_coe_nnnorm]
  have h : ∀ᵐ x ∂ν, ENNReal.ofReal (μ.rnDeriv ν x).toReal = μ.rnDeriv ν x := by
    filter_upwards [Measure.rnDeriv_ne_top μ ν] with x hx
    rw [ENNReal.ofReal_toReal hx]
  have h' : ∀ᵐ x ∂ν, ENNReal.ofReal (μ.rnDeriv ν x).toReal * ‖f x‖₊ = μ.rnDeriv ν x * ‖f x‖₊ := by
    filter_upwards [h] with x hx using by rw [hx]
  rw [lintegral_congr_ae h']
  change ∫⁻ a, (μ.rnDeriv ν * (fun a ↦ (‖f a‖₊ : ℝ≥0∞))) a ∂ν < ⊤
  rw [← lintegral_withDensity_eq_lintegral_mul_non_measurable]
  · rw [Measure.withDensity_rnDeriv_eq _ _ hμν]
    exact h_int.2
  · exact Measure.measurable_rnDeriv _ _
  · exact Measure.rnDeriv_lt_top _ _

lemma integral_llr_nonneg_aux' {μ ν : Measure α} [IsFiniteMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) (h_int : Integrable (LLR μ ν) μ) :
    (μ Set.univ).toReal * log (μ Set.univ).toReal ≤ ∫ x, LLR μ ν x ∂μ := by
  have h_eq_int : (μ Set.univ).toReal = ∫ x, (μ.rnDeriv ν x).toReal ∂ν := by
    conv_lhs => rw [← Measure.withDensity_rnDeriv_eq _ _ hμν]
    simp only [MeasurableSet.univ, withDensity_apply, Measure.restrict_univ]
    rw [integral_toReal]
    · exact (Measure.measurable_rnDeriv _ _).aemeasurable
    · exact Measure.rnDeriv_lt_top _ _
  let φ : ℝ → ℝ := fun x ↦ x * log x
  calc (μ Set.univ).toReal * log (μ Set.univ).toReal
    = φ (μ Set.univ).toReal := rfl
  _ = φ (∫ x, (μ.rnDeriv ν x).toReal ∂ν) := by rw [h_eq_int]
  _ ≤ ∫ x, φ (μ.rnDeriv ν x).toReal ∂ν := by
    rw [← average_eq_integral, ← average_eq_integral]
    refine ConvexOn.map_average_le Real.convexOn_id_mul_log Real.continuous_id_mul_log.continuousOn
      isClosed_Ici ?_ Measure.integrable_toReal_rnDeriv ?_
    · simp
    · exact integrable_toReal_rnDeriv_mul hμν h_int
        (stronglyMeasurable_llr _ _).aestronglyMeasurable
  _ = ∫ x, (μ.rnDeriv ν x).toReal * log (μ.rnDeriv ν x).toReal ∂ν := rfl
  _ = ∫ x, LLR μ ν x ∂μ := by
    simp_rw [LLR]
    conv_rhs =>
      rw [← Measure.withDensity_rnDeriv_eq _ _ hμν]
      conv in (Measure.rnDeriv (ν.withDensity (μ.rnDeriv ν)) ν) =>
        rw [Measure.withDensity_rnDeriv_eq _ _ hμν]
    have h_rn_eq : μ.rnDeriv ν =ᵐ[ν] fun x ↦ (μ.rnDeriv ν x).toNNReal := by
      filter_upwards [Measure.rnDeriv_lt_top μ ν] with x hx
      rw [ENNReal.coe_toNNReal]
      exact hx.ne
    have h_ν_eq : ν.withDensity (μ.rnDeriv ν)
        = ν.withDensity (fun x ↦ (μ.rnDeriv ν x).toNNReal) := withDensity_congr_ae h_rn_eq
    conv_rhs => rw [h_ν_eq]
    rw [integral_withDensity_eq_integral_smul]
    swap; · exact (Measure.measurable_rnDeriv _ _).ennreal_toNNReal
    congr

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
  refine le_trans ?_ (integral_llr_nonneg_aux' hμν h_int)
  simp only [measure_univ, ENNReal.one_toReal, log_one, mul_zero, le_refl]

end integral_llr_nonneg

section llr_tilted

lemma llr_tilted_ae_eq {μ ν : Measure α} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμν : μ ≪ ν) {f : α → ℝ} (h_int : Integrable (fun x ↦ exp (f x)) ν) :
    (LLR μ (ν.tilted f)) =ᵐ[μ] fun x ↦ - f x + logIntegralExp ν f + LLR μ ν x := by
  filter_upwards [hμν.ae_le (rnDeriv_tilted_right μ ν h_int), Measure.rnDeriv_pos hμν,
    hμν.ae_le (Measure.rnDeriv_lt_top μ ν)] with x hx hx_pos hx_lt_top
  rw [LLR, hx, log_mul (exp_pos _).ne']
  · rw [log_exp, LLR]
  · rw [ne_eq, ENNReal.toReal_eq_zero_iff]
    simp only [hx_pos.ne', hx_lt_top.ne, or_self, not_false_eq_true]

lemma integrable_llr_tilted {μ ν : Measure α} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμν : μ ≪ ν) {f : α → ℝ} (hfμ : Integrable f μ)
    (hfν : Integrable (fun x ↦ exp (f x)) ν) (h_int : Integrable (LLR μ ν) μ) :
    Integrable (LLR μ (ν.tilted f)) μ := by
  rw [integrable_congr (llr_tilted_ae_eq hμν hfν)]
  exact Integrable.add (hfμ.neg.add (integrable_const _)) h_int

lemma integral_llr_tilted {μ ν : Measure α} [IsProbabilityMeasure μ] [IsFiniteMeasure ν]
    {f : α → ℝ} (hμν : μ ≪ ν) (hfμ : Integrable f μ) (hfν : Integrable (fun x ↦ exp (f x)) ν)
    (h_int : Integrable (LLR μ ν) μ) :
    ∫ x, LLR μ (ν.tilted f) x ∂μ = ∫ x, LLR μ ν x ∂μ - ∫ x, f x ∂μ + logIntegralExp ν f := by
  calc ∫ x, LLR μ (ν.tilted f) x ∂μ
    = ∫ x, - f x + logIntegralExp ν f + LLR μ ν x ∂μ := integral_congr_ae (llr_tilted_ae_eq hμν hfν)
  _ = - ∫ x, f x ∂μ + logIntegralExp ν f + ∫ x, LLR μ ν x ∂μ := by
        rw [← integral_neg, integral_add ?_ h_int]
        swap; · exact hfμ.neg.add (integrable_const _)
        rw [integral_add ?_ (integrable_const _)]
        swap; · exact hfμ.neg
        simp only [integral_const, measure_univ, ENNReal.one_toReal, smul_eq_mul, one_mul]
  _ = ∫ x, LLR μ ν x ∂μ - ∫ x, f x ∂μ + logIntegralExp ν f := by abel

end llr_tilted

lemma integral_sub_logIntegralExp_le {μ ν : Measure α}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) (h_int : Integrable (LLR μ ν) μ)
    (f : α → ℝ) (hfμ : Integrable f μ) (hf : Integrable (fun x ↦ exp (f x)) ν) :
    ∫ x, f x ∂μ - logIntegralExp ν f ≤ ∫ x, LLR μ ν x ∂μ := by
  have : ∫ x, LLR μ ν x ∂μ - ∫ x, LLR μ (ν.tilted f) x ∂μ = ∫ x, f x ∂μ - logIntegralExp ν f := by
    rw [integral_llr_tilted hμν hfμ hf h_int]
    abel
  rw [← this]
  simp only [tsub_le_iff_right, le_add_iff_nonneg_right]
  have : IsProbabilityMeasure (Measure.tilted ν f) := isProbabilityMeasure_tilted hf
  have hf_m : AEMeasurable f ν := aemeasurable_of_aemeasurable_exp hf.1.aemeasurable
  refine integral_llr_nonneg (hμν.trans (absolutelyContinuous_tilted hf_m)) ?_
  exact integrable_llr_tilted hμν hfμ hf h_int

lemma ciSup_le_integral_llr {μ ν : Measure α} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) (h_int : Integrable (LLR μ ν) μ) :
    ⨆ (f : α → ℝ) (_ : Integrable f μ)
        (_ : Integrable (fun x ↦ exp (f x)) ν), ∫ x, f x ∂μ - logIntegralExp ν f
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

lemma stronglyMeasurable_llrAddConst {μ ν : Measure α} {u : ℝ} :
    StronglyMeasurable (LLRAddConst μ ν u) :=
  ((measurable_toReal_rnDeriv _ _).add measurable_const).log.stronglyMeasurable

lemma log_le_llrAddConst {μ ν : Measure α} {u : ℝ} {x : α} (hu : 0 < u) :
    log u ≤ LLRAddConst μ ν u x := by
  rw [LLRAddConst, Real.log_le_log hu]
  · simp
  · positivity

lemma llrAddConst_le_log_max {μ ν : Measure α} {u : ℝ} {x : α} (hu : 0 < u) :
    LLRAddConst μ ν u x ≤ log (max (μ.rnDeriv ν x).toReal u) + log 2 := by
  rw [← log_mul _ two_ne_zero]
  swap; · refine ne_of_gt ?_; positivity
  rw [LLRAddConst, Real.log_le_log]
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
    logIntegralExp ν (LLRAddConst μ ν u) = log (1 + u) := by
  simp_rw [logIntegralExp, exp_llrAddConst hu]
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
  rw [LLR, LLRAddConst, Real.log_le_log]
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
      ∫ x, LLRAddConst μ ν u' x ∂μ - logIntegralExp ν (LLRAddConst μ ν u')) + log (1 + u) := by
    calc ∫ x, LLRAddConst μ ν u x ∂μ
      = ∫ x, LLRAddConst μ ν u x ∂μ - logIntegralExp ν (LLRAddConst μ ν u)
        + logIntegralExp ν (LLRAddConst μ ν u) := by abel
    _ ≤ (⨆ u : {v // (0 : ℝ) < v},
          ∫ x, LLRAddConst μ ν u x ∂μ - logIntegralExp ν (LLRAddConst μ ν u))
        + logIntegralExp ν (LLRAddConst μ ν u) := by
          refine add_le_add ?_ le_rfl
          refine le_ciSup_of_le ?_ ⟨u, hu⟩ le_rfl
          refine ⟨∫ x, LLR μ ν x ∂μ, fun y ⟨u, huy⟩ ↦ ?_⟩
          rw [← huy]
          exact integral_sub_logIntegralExp_le hμν h_int (LLRAddConst μ ν _)
            (integrable_llrAddConst u.2.le h_int) (integrable_exp_llrAddConst u.2)
    _ = (⨆ u : {v // (0 : ℝ) < v},
          ∫ x, LLRAddConst μ ν u x ∂μ - logIntegralExp ν (LLRAddConst μ ν u))
        + log (1 + u) := by rw [logIntegralExp_llrAddConst hμν hu]

lemma integral_llr_le_ciSup_integral_llrAddConst_sub {μ ν : Measure α}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) (h_int : Integrable (LLR μ ν) μ) :
    ∫ x, LLR μ ν x ∂μ ≤ ⨆ u : {v // (0 : ℝ) < v},
      ∫ x, LLRAddConst μ ν u x ∂μ - logIntegralExp ν (LLRAddConst μ ν u) := by
    have h_bdd : BddBelow (Set.range fun u : {v // (0 : ℝ) < v} ↦ log (1 + u)) := by
      refine ⟨0, fun y ⟨u, huy⟩ ↦ ?_⟩
      rw [← huy]
      refine log_nonneg ?_
      simp [u.2.le]
    calc ∫ x, LLR μ ν x ∂μ
      ≤ ⨅ u : {v // (0 : ℝ) < v}, ∫ x, LLRAddConst μ ν u x ∂μ :=
          integral_llr_le_ciInf_integral_llrAddConst hμν h_int
    _ ≤ ⨅ u : {v // (0 : ℝ) < v}, (⨆ u' : {v // (0 : ℝ) < v},
        ∫ x, LLRAddConst μ ν u' x ∂μ - logIntegralExp ν (LLRAddConst μ ν u')) + log (1 + u) := by
          refine ciInf_mono ?_ ?_
          · refine ⟨∫ x, LLR μ ν x ∂μ, fun y ⟨u, huy⟩ ↦ ?_⟩
            rw [← huy]
            exact integral_llr_le_integral_llrAddConst u.2.le hμν h_int
          · exact fun u ↦ integral_llrAddConst_le_ciSup_add hμν h_int u.2
    _ = (⨆ u' : {v // (0 : ℝ) < v},
          ∫ x, LLRAddConst μ ν u' x ∂μ - logIntegralExp ν (LLRAddConst μ ν u'))
        + ⨅ u : {v // (0 : ℝ) < v}, log (1 + u) := by
          rw [← add_ciInf h_bdd]
    _ = ⨆ u : {v // (0 : ℝ) < v},
        ∫ x, LLRAddConst μ ν u x ∂μ - logIntegralExp ν (LLRAddConst μ ν u) := by
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
        ∫ x, f x ∂μ - logIntegralExp ν f := by
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

theorem DonskerVaradhan {μ ν : Measure α} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) (h_int : Integrable (LLR μ ν) μ) :
    ∫ x, LLR μ ν x ∂μ
      = ⨆ (f : α → ℝ) (_ : Integrable f μ) (_ : Integrable (fun x ↦ exp (f x)) ν),
        ∫ x, f x ∂μ - logIntegralExp ν f :=
  le_antisymm (integral_llr_le_ciSup hμν h_int) (ciSup_le_integral_llr hμν h_int)

-- TODO: this should be in EReal?
noncomputable
def KL (μ ν : Measure α) [Decidable (μ ≪ ν)] [Decidable (Integrable (LLR μ ν) μ)] : ℝ≥0∞ :=
  if μ ≪ ν ∧ Integrable (LLR μ ν) μ then ENNReal.ofReal (∫ x, LLR μ ν x ∂μ) else ∞

end MeasureTheory
