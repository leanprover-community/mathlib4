/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Analysis.Convex.Integral

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

section x_log_x

namespace Real

lemma continuous_id_mul_log : Continuous (fun x ↦ x * log x) := by
  sorry

lemma convexOn_id_mul_log : ConvexOn ℝ (Set.Ici (0 : ℝ)) (fun x ↦ x * log x) := by
  sorry

lemma id_mul_log_ge {x : ℝ} (hx : 0 ≤ x) : log (exp 1) / (exp 1) ≤ x * log x := by
  sorry

lemma id_mul_log_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ x * log x :=
  mul_nonneg (zero_le_one.trans hx) (log_nonneg hx)

lemma measurable_id_mul_log : Measurable (fun x ↦ x * log x) :=
  measurable_id'.mul measurable_log

end Real

end x_log_x

section LLR

lemma measurable_toReal_rnDeriv (μ ν : Measure α) : Measurable (fun x ↦ (μ.rnDeriv ν x).toReal) :=
  (Measure.measurable_rnDeriv μ ν).ennreal_toReal

lemma stronglyMeasurable_toReal_rnDeriv (μ ν : Measure α) :
    StronglyMeasurable (fun x ↦ (μ.rnDeriv ν x).toReal) :=
  (measurable_toReal_rnDeriv μ ν).stronglyMeasurable

/-- Log-Likelihood Ratio. -/
noncomputable
def LLR (μ ν : Measure α) (x : α) : ℝ := log (μ.rnDeriv ν x).toReal

lemma LLR_def (μ ν : Measure α) : LLR μ ν = fun x ↦ log (μ.rnDeriv ν x).toReal := rfl

lemma exp_LLR (μ ν : Measure α) [SigmaFinite μ] :
    (fun x ↦ exp (LLR μ ν x))
      =ᵐ[ν] fun x ↦ if μ.rnDeriv ν x = 0 then 1 else (μ.rnDeriv ν x).toReal := by
  filter_upwards [Measure.rnDeriv_lt_top μ ν] with x hx
  by_cases h_zero : μ.rnDeriv ν x = 0
  · simp only [LLR, h_zero, ENNReal.zero_toReal, log_zero, exp_zero, ite_true]
  rw [LLR, exp_log, if_neg h_zero]
  rw [ENNReal.toReal_pos_iff]
  exact ⟨lt_of_le_of_ne (zero_le _) (Ne.symm h_zero), hx⟩

lemma measurable_LLR (μ ν : Measure α) : Measurable (LLR μ ν) :=
  (measurable_toReal_rnDeriv μ ν).log

lemma stronglyMeasurable_LLR (μ ν : Measure α) : StronglyMeasurable (LLR μ ν) :=
  (measurable_LLR μ ν).stronglyMeasurable

lemma LLR_smul_left {μ ν : Measure α} [IsFiniteMeasure μ] [Measure.HaveLebesgueDecomposition μ ν]
    (hμν : μ ≪ ν) (c : ℝ≥0∞) (hc : c ≠ 0) (hc_ne_top : c ≠ ∞) :
    LLR (c • μ) ν =ᵐ[μ] fun x ↦ LLR μ ν x + log c.toReal := by
  simp only [LLR, LLR_def]
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

lemma LLR_smul_right {μ ν : Measure α} [IsFiniteMeasure μ] [Measure.HaveLebesgueDecomposition μ ν]
    (hμν : μ ≪ ν) (c : ℝ≥0∞) (hc : c ≠ 0) (hc_ne_top : c ≠ ∞) :
    LLR μ (c • ν) =ᵐ[μ] fun x ↦ LLR μ ν x - log c.toReal := by
  simp only [LLR, LLR_def]
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

section definition

-- TODO: this should be in EReal?
noncomputable
def KL (μ ν : Measure α) [Decidable (μ ≪ ν)] [Decidable (Integrable (LLR μ ν) μ)] : ℝ≥0∞ :=
  if μ ≪ ν ∧ Integrable (LLR μ ν) μ then ENNReal.ofReal (∫ x, LLR μ ν x ∂μ) else ∞

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

lemma integral_LLR_nonneg_aux' {μ ν : Measure α} [IsFiniteMeasure μ] [IsProbabilityMeasure ν]
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
        (stronglyMeasurable_LLR _ _).aestronglyMeasurable
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

lemma integral_LLR_ge {μ ν : Measure α} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
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
  have h := integral_LLR_nonneg_aux' (?_ : μ ≪ ν') ?_
  rotate_left
  · refine Measure.AbsolutelyContinuous.trans hμν ?_
    refine Measure.absolutelyContinuous_of_le_smul (c := ν Set.univ) ?_
    rw [← smul_assoc, smul_eq_mul, ENNReal.mul_inv_cancel, one_smul]
    · simp [hν]
    · exact measure_ne_top _ _
  · rw [integrable_congr (LLR_smul_right hμν (ν Set.univ)⁻¹ _ _)]
    rotate_left
    · simp [measure_ne_top ν _]
    · simp [hν]
    exact h_int.sub (integrable_const _)
  rw [integral_congr_ae (LLR_smul_right hμν (ν Set.univ)⁻¹ _ _)] at h
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

lemma integral_LLR_nonneg
    {μ ν : Measure α} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) (h_int : Integrable (LLR μ ν) μ) :
    0 ≤ ∫ x, LLR μ ν x ∂μ := by
  refine le_trans ?_ (integral_LLR_nonneg_aux' hμν h_int)
  simp only [measure_univ, ENNReal.one_toReal, log_one, mul_zero, le_refl]

end definition

lemma LLR_tilted_ae_eq {μ ν : Measure α} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) {f : α → ℝ} (hf : AEMeasurable f ν) (h_int : Integrable (fun x ↦ exp (f x)) ν) :
    (LLR μ (ν.tilted f)) =ᵐ[μ] fun x ↦ - f x + logIntegralExp ν f + LLR μ ν x := by
  filter_upwards [hμν.ae_le (rnDeriv_tilted_right μ ν hf h_int), Measure.rnDeriv_pos hμν,
    hμν.ae_le (Measure.rnDeriv_lt_top μ ν)] with x hx hx_pos hx_lt_top
  rw [LLR, hx, log_mul (exp_pos _).ne']
  · rw [log_exp, LLR]
  · rw [ne_eq, ENNReal.toReal_eq_zero_iff]
    simp only [hx_pos.ne', hx_lt_top.ne, or_self, not_false_eq_true]

lemma integrable_LLR_tilted
    {μ ν : Measure α} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) {f : α → ℝ} (hf : AEMeasurable f ν) (hfμ : Integrable f μ)
    (hfν : Integrable (fun x ↦ exp (f x)) ν)
    (h_int : Integrable (LLR μ ν) μ) :
    Integrable (LLR μ (ν.tilted f)) μ := by
  rw [integrable_congr (LLR_tilted_ae_eq hμν hf hfν)]
  exact Integrable.add (hfμ.neg.add (integrable_const _)) h_int

lemma todo_aux {μ ν : Measure α} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {f : α → ℝ}
    (hμν : μ ≪ ν) (hfμ : Integrable f μ) (hfν : Integrable (fun x ↦ exp (f x)) ν)
    (h_int : Integrable (LLR μ ν) μ) :
    ∫ x, LLR μ ν x ∂μ - ∫ x, LLR μ (ν.tilted f) x ∂μ = ∫ x, f x ∂μ - logIntegralExp ν f := by
  calc ∫ x, LLR μ ν x  ∂μ - ∫ x, LLR μ (ν.tilted f) x ∂μ
    = ∫ x, LLR μ ν x ∂μ - ∫ x, - f x + logIntegralExp ν f + LLR μ ν x ∂μ := by
        refine congr_arg₂ _ rfl ?_
        refine integral_congr_ae (LLR_tilted_ae_eq hμν ?_ hfν)
        exact aemeasurable_of_aemeasurable_exp hfν.1.aemeasurable
  _ = ∫ x, LLR μ ν x ∂μ - (- ∫ x, f x ∂μ + logIntegralExp ν f + ∫ x, LLR μ ν x ∂μ) := by
        congr
        rw [← integral_neg, integral_add ?_ h_int]
        swap; · exact hfμ.neg.add (integrable_const _)
        rw [integral_add ?_ (integrable_const _)]
        swap; · exact hfμ.neg
        simp only [integral_const, measure_univ, ENNReal.one_toReal, smul_eq_mul, one_mul]
  _ = ∫ x, f x ∂μ - logIntegralExp ν f := by abel

-- TODO name
lemma some_le {μ ν : Measure α} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) (h_int : Integrable (LLR μ ν) μ)
    (f : α → ℝ) (hfμ : Integrable f μ) (hf : Integrable (fun x ↦ exp (f x)) ν) :
    ∫ x, f x ∂μ - logIntegralExp ν f ≤ ∫ x, LLR μ ν x ∂μ := by
  rw [← todo_aux hμν hfμ hf h_int]
  simp only [tsub_le_iff_right, le_add_iff_nonneg_right]
  have : IsProbabilityMeasure (Measure.tilted ν f) := isProbabilityMeasure_tilted hf
  have hf_m : AEMeasurable f ν := aemeasurable_of_aemeasurable_exp hf.1.aemeasurable
  refine integral_LLR_nonneg (hμν.trans (absolutelyContinuous_tilted hf_m)) ?_
  exact integrable_LLR_tilted hμν hf_m hfμ hf h_int

lemma todo' {μ ν : Measure α} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) (h_int : Integrable (LLR μ ν) μ) :
    ⨆ (f : α → ℝ) (_ : Integrable f μ)
        (_ : Integrable (fun x ↦ exp (f x)) ν), ∫ x, f x ∂μ - logIntegralExp ν f
      ≤ ∫ x, LLR μ ν x ∂μ := by
  refine ciSup_le (fun f ↦ ?_)
  by_cases hfμ : Integrable f μ
  · simp only [hfμ, ciSup_unique]
    by_cases hf : Integrable (fun x ↦ exp (f x)) ν
    · simp only [hf, ciSup_unique]
      exact some_le hμν h_int f hfμ hf
    · simp [hf, ciSup_empty]
      exact integral_LLR_nonneg hμν h_int
  · simp only [hfμ, ciSup_empty]
    exact integral_LLR_nonneg hμν h_int

lemma aux_bddAbove {μ ν : Measure α} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) (h_int : Integrable (LLR μ ν) μ) :
    BddAbove (Set.range fun f ↦ ⨆ (_ : Integrable f μ) (_ : Integrable (fun x ↦ exp (f x)) ν),
      ∫ x, f x ∂μ - logIntegralExp ν f) := by
  refine ⟨∫ x, LLR μ ν x ∂μ, ?_⟩
  rw [mem_upperBounds]
  intro x
  simp only [Set.mem_range, ge_iff_le, le_max_iff, forall_exists_index]
  rintro f rfl
  by_cases hfμ : Integrable f μ
  · simp only [hfμ, ciSup_unique]
    by_cases hf : Integrable (fun x ↦ exp (f x)) ν
    · simp only [hf, ciSup_unique]
      exact some_le hμν h_int f hfμ hf
    · simp only [hf, ciSup_empty]
      exact integral_LLR_nonneg hμν h_int
  · simp only [hfμ, ciSup_empty]
    exact integral_LLR_nonneg hμν h_int

lemma todo {μ ν : Measure α} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) (h_int : Integrable (LLR μ ν) μ) :
    ∫ x, LLR μ ν x ∂μ
      ≤ ⨆ (f : α → ℝ) (_ : Integrable f μ) (_ : Integrable (fun x ↦ exp (f x)) ν),
        ∫ x, f x ∂μ - logIntegralExp ν f := by
  classical
  let LLRu : ℝ → α → ℝ := fun u x ↦ log ((μ.rnDeriv ν x).toReal + u)
  have hu_int : ∀ u, Integrable (LLRu u) μ := by
    sorry
  have h_exp_log : ∀ (u) (hu : 0 < u) (x),
      exp (log ((μ.rnDeriv ν x).toReal + u)) = (μ.rnDeriv ν x).toReal + u := by
    intro u hu x
    rw [exp_log]
    positivity
  have hu_exp_int : ∀ u, 0 < u → Integrable (fun x ↦ exp (LLRu u x)) ν := by
    intro u hu
    simp_rw [h_exp_log u hu]
    exact Measure.integrable_toReal_rnDeriv.add (integrable_const _)
  have hu_le : ∫ x, LLR μ ν x ∂μ ≤ ⨅ (u : {v // (0 : ℝ) < v}), ∫ x, LLRu u x ∂μ := by
    refine le_ciInf (fun u ↦ ?_)
    suffices LLR μ ν ≤ᵐ[μ] LLRu u by exact integral_mono_ae h_int (hu_int _) this
    filter_upwards [Measure.rnDeriv_pos hμν, hμν.ae_le (Measure.rnDeriv_lt_top μ ν)]
      with a ha_pos ha_lt_top
    simp only [LLR]
    rw [← exp_le_exp, exp_log, exp_log]
    · rw [le_add_iff_nonneg_right]
      exact u.2.le
    · have hu_pos := u.2
      positivity
    · rw [ENNReal.toReal_pos_iff]
      simp [ha_pos, ha_lt_top]
  refine hu_le.trans ?_
  suffices ∀ u, 0 < u → ∫ x, LLRu u x ∂μ
      ≤ (⨆ (f : α → ℝ) (_ : Integrable f μ) (_ : Integrable (fun x ↦ exp (f x)) ν),
        ∫ x, f x ∂μ - logIntegralExp ν f + log (1 + u)) by
    sorry
  intro u hu
  suffices ∫ x, LLRu u x ∂μ = ∫ x, LLRu u x ∂μ - logIntegralExp ν (LLRu u) + log (1 + u) by
    rw [this]
    refine le_ciSup_of_le ?_ (LLRu u) ?_
    · refine ⟨∫ x, LLR μ ν x ∂μ + log (1 + u), ?_⟩
      rw [mem_upperBounds]
      intro x
      simp only [Set.mem_range, ge_iff_le, le_max_iff, forall_exists_index]
      rintro f rfl
      by_cases hfμ : Integrable f μ
      · simp only [hfμ, ciSup_unique]
        by_cases hf : Integrable (fun x ↦ exp (f x)) ν
        · simp only [hf, ciSup_unique]
          refine add_le_add ?_ le_rfl
          exact some_le hμν h_int f hfμ hf
        · simp only [hf, ciSup_empty]
          refine add_nonneg (integral_LLR_nonneg hμν h_int) ?_
          refine log_nonneg ?_
          simp only [le_add_iff_nonneg_right, hu.le]
      · simp only [hfμ, ciSup_empty]
        refine add_nonneg (integral_LLR_nonneg hμν h_int) ?_
        refine log_nonneg ?_
        simp only [le_add_iff_nonneg_right, hu.le]
    · simp only [hu_int u, hu_exp_int u hu, ciSup_unique]
      exact le_rfl
  suffices logIntegralExp ν (LLRu u) = log (1 + u) by
    rw [this]
    abel
  simp_rw [logIntegralExp, h_exp_log u hu]
  rw [integral_add Measure.integrable_toReal_rnDeriv (integrable_const _), integral_const]
  simp only [measure_univ, ENNReal.one_toReal, smul_eq_mul, one_mul]
  congr
  rw [Measure.integral_toReal_rnDeriv hμν]
  simp only [measure_univ, ENNReal.one_toReal]

-- todo: differs from the usual statement due to the `Integrable f μ` assumption
theorem DV' {μ ν : Measure α} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) (h_int : Integrable (LLR μ ν) μ) :
    ∫ x, LLR μ ν x ∂μ
      = ⨆ (f : α → ℝ) (_ : Integrable f μ) (_ : Integrable (fun x ↦ exp (f x)) ν),
        ∫ x, f x ∂μ - logIntegralExp ν f :=
  le_antisymm (todo hμν h_int) (todo' hμν h_int)

end MeasureTheory
