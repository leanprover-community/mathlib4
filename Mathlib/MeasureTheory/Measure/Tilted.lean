/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# Exponentially tilted measures

The exponential tilting of a measure `μ` on `α` by a function `f : α → ℝ` is the measure with
density `x ↦ exp (f x) / ∫ y, exp (f y) ∂μ` with respect to `μ`. This is sometimes also called
the Esscher transform.

The definition is mostly used for `f` linear, in which case the exponentially tilted measure belongs
to the natural exponential family of the base measure. Exponentially tilted measures for general `f`
can be used for example to establish variational expressions for the Kullback-Leibler divergence.

## Main definitions

* `Measure.tilted μ f`: exponential tilting of `μ` by `f`, equal to
  `μ.withDensity (fun x ↦ ENNReal.ofReal (exp (f x) / ∫ x, exp (f x) ∂μ))`.

-/

open Real

open scoped ENNReal NNReal

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α} {f : α → ℝ}

/-- Exponentially tilted measure. When `x ↦ exp (f x)` is integrable, `μ.tilted f` is the
probability measure with density with respect to `μ` proportional to `exp (f x)`. Otherwise it is 0.
-/
noncomputable
def Measure.tilted (μ : Measure α) (f : α → ℝ) : Measure α :=
  μ.withDensity (fun x ↦ ENNReal.ofReal (exp (f x) / ∫ x, exp (f x) ∂μ))

@[simp]
lemma tilted_of_not_integrable (hf : ¬ Integrable (fun x ↦ exp (f x)) μ) : μ.tilted f = 0 := by
  rw [Measure.tilted, integral_undef hf]
  simp

@[simp]
lemma tilted_of_not_aemeasurable (hf : ¬ AEMeasurable f μ) : μ.tilted f = 0 := by
  refine tilted_of_not_integrable ?_
  suffices ¬ AEMeasurable (fun x ↦ exp (f x)) μ by exact fun h ↦ this h.1.aemeasurable
  exact fun h ↦ hf (aemeasurable_of_aemeasurable_exp h)

@[simp]
lemma tilted_zero_measure (f : α → ℝ) : (0 : Measure α).tilted f = 0 := by simp [Measure.tilted]

@[simp]
lemma tilted_const' (μ : Measure α) (c : ℝ) :
    μ.tilted (fun _ ↦ c) = (μ Set.univ)⁻¹ • μ := by
  cases eq_zero_or_neZero μ with
  | inl h => rw [h]; simp
  | inr h0 =>
    simp only [Measure.tilted, withDensity_const, integral_const, smul_eq_mul]
    by_cases h_univ : μ Set.univ = ∞
    · simp only [measureReal_def, h_univ, ENNReal.toReal_top, zero_mul, div_zero,
      ENNReal.ofReal_zero, zero_smul, ENNReal.inv_top]
    congr
    rw [div_eq_mul_inv, mul_inv, mul_comm, mul_assoc, inv_mul_cancel₀ (exp_pos _).ne', mul_one,
      measureReal_def, ← ENNReal.toReal_inv, ENNReal.ofReal_toReal]
    simp [h0.out]

lemma tilted_const (μ : Measure α) [IsProbabilityMeasure μ] (c : ℝ) :
    μ.tilted (fun _ ↦ c) = μ := by simp

@[simp]
lemma tilted_zero' (μ : Measure α) : μ.tilted 0 = (μ Set.univ)⁻¹ • μ := by
  change μ.tilted (fun _ ↦ 0) = (μ Set.univ)⁻¹ • μ
  simp

lemma tilted_zero (μ : Measure α) [IsProbabilityMeasure μ] : μ.tilted 0 = μ := by simp

lemma tilted_congr {g : α → ℝ} (hfg : f =ᵐ[μ] g) :
    μ.tilted f = μ.tilted g := by
  have h_int_eq : ∫ x, exp (f x) ∂μ = ∫ x, exp (g x) ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hfg] with x hx
    rw [hx]
  refine withDensity_congr_ae ?_
  filter_upwards [hfg] with x hx
  rw [h_int_eq, hx]

lemma tilted_eq_withDensity_nnreal (μ : Measure α) (f : α → ℝ) :
    μ.tilted f = μ.withDensity (fun x ↦ ((↑) : ℝ≥0 → ℝ≥0∞)
      (⟨exp (f x) / ∫ x, exp (f x) ∂μ, by positivity⟩ : ℝ≥0)) := by
  rw [Measure.tilted]
  congr with x
  rw [ENNReal.ofReal_eq_coe_nnreal]

lemma tilted_apply' (μ : Measure α) (f : α → ℝ) {s : Set α} (hs : MeasurableSet s) :
    μ.tilted f s = ∫⁻ a in s, ENNReal.ofReal (exp (f a) / ∫ x, exp (f x) ∂μ) ∂μ := by
  rw [Measure.tilted, withDensity_apply _ hs]

lemma tilted_apply (μ : Measure α) [SFinite μ] (f : α → ℝ) (s : Set α) :
    μ.tilted f s = ∫⁻ a in s, ENNReal.ofReal (exp (f a) / ∫ x, exp (f x) ∂μ) ∂μ := by
  rw [Measure.tilted, withDensity_apply' _ s]

lemma tilted_apply_eq_ofReal_integral' {s : Set α} (f : α → ℝ) (hs : MeasurableSet s) :
    μ.tilted f s = ENNReal.ofReal (∫ a in s, exp (f a) / ∫ x, exp (f x) ∂μ ∂μ) := by
  by_cases hf : Integrable (fun x ↦ exp (f x)) μ
  · rw [tilted_apply' _ _ hs, ← ofReal_integral_eq_lintegral_ofReal]
    · exact hf.integrableOn.div_const _
    · exact ae_of_all _ (fun _ ↦ by positivity)
  · simp only [hf, not_false_eq_true, tilted_of_not_integrable, Measure.coe_zero,
      Pi.zero_apply, integral_undef hf, div_zero, integral_zero, ENNReal.ofReal_zero]

lemma tilted_apply_eq_ofReal_integral [SFinite μ] (f : α → ℝ) (s : Set α) :
    μ.tilted f s = ENNReal.ofReal (∫ a in s, exp (f a) / ∫ x, exp (f x) ∂μ ∂μ) := by
  by_cases hf : Integrable (fun x ↦ exp (f x)) μ
  · rw [tilted_apply _ _, ← ofReal_integral_eq_lintegral_ofReal]
    · exact hf.integrableOn.div_const _
    · exact ae_of_all _ (fun _ ↦ by positivity)
  · simp [tilted_of_not_integrable hf, integral_undef hf]

lemma isProbabilityMeasure_tilted [NeZero μ] (hf : Integrable (fun x ↦ exp (f x)) μ) :
    IsProbabilityMeasure (μ.tilted f) := by
  constructor
  simp_rw [tilted_apply' _ _ MeasurableSet.univ, setLIntegral_univ,
    ENNReal.ofReal_div_of_pos (integral_exp_pos hf), div_eq_mul_inv]
  rw [lintegral_mul_const'' _ hf.1.aemeasurable.ennreal_ofReal,
    ← ofReal_integral_eq_lintegral_ofReal hf (ae_of_all _ fun _ ↦ (exp_pos _).le),
    ENNReal.mul_inv_cancel]
  · simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact integral_exp_pos hf
  · simp

instance isZeroOrProbabilityMeasure_tilted : IsZeroOrProbabilityMeasure (μ.tilted f) := by
  rcases eq_zero_or_neZero μ with hμ | hμ
  · simp only [hμ, tilted_zero_measure]
    infer_instance
  by_cases hf : Integrable (fun x ↦ exp (f x)) μ
  · have := isProbabilityMeasure_tilted hf
    infer_instance
  · simp only [hf, not_false_eq_true, tilted_of_not_integrable]
    infer_instance

section lintegral

lemma setLIntegral_tilted' (f : α → ℝ) (g : α → ℝ≥0∞) {s : Set α} (hs : MeasurableSet s) :
    ∫⁻ x in s, g x ∂(μ.tilted f)
      = ∫⁻ x in s, ENNReal.ofReal (exp (f x) / ∫ x, exp (f x) ∂μ) * g x ∂μ := by
  by_cases hf : AEMeasurable f μ
  · rw [Measure.tilted, setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable₀]
    · simp only [Pi.mul_apply]
    · refine AEMeasurable.restrict ?_
      exact ((measurable_exp.comp_aemeasurable hf).div_const _).ennreal_ofReal
    · exact hs
    · filter_upwards
      simp only [ENNReal.ofReal_lt_top, implies_true]
  · have hf' : ¬ Integrable (fun x ↦ exp (f x)) μ := by
      exact fun h ↦ hf (aemeasurable_of_aemeasurable_exp h.1.aemeasurable)
    simp only [hf, not_false_eq_true, tilted_of_not_aemeasurable, Measure.restrict_zero,
      lintegral_zero_measure]
    rw [integral_undef hf']
    simp

lemma setLIntegral_tilted [SFinite μ] (f : α → ℝ) (g : α → ℝ≥0∞) (s : Set α) :
    ∫⁻ x in s, g x ∂(μ.tilted f)
      = ∫⁻ x in s, ENNReal.ofReal (exp (f x) / ∫ x, exp (f x) ∂μ) * g x ∂μ := by
  by_cases hf : AEMeasurable f μ
  · rw [Measure.tilted, setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable₀']
    · simp only [Pi.mul_apply]
    · refine AEMeasurable.restrict ?_
      exact ((measurable_exp.comp_aemeasurable hf).div_const _).ennreal_ofReal
    · filter_upwards
      simp only [ENNReal.ofReal_lt_top, implies_true]
  · have hf' : ¬ Integrable (fun x ↦ exp (f x)) μ := by
      exact fun h ↦ hf (aemeasurable_of_aemeasurable_exp h.1.aemeasurable)
    simp only [hf, not_false_eq_true, tilted_of_not_aemeasurable, Measure.restrict_zero,
      lintegral_zero_measure]
    rw [integral_undef hf']
    simp

lemma lintegral_tilted (f : α → ℝ) (g : α → ℝ≥0∞) :
    ∫⁻ x, g x ∂(μ.tilted f)
      = ∫⁻ x, ENNReal.ofReal (exp (f x) / ∫ x, exp (f x) ∂μ) * (g x) ∂μ := by
  rw [← setLIntegral_univ, setLIntegral_tilted' f g MeasurableSet.univ, setLIntegral_univ]

end lintegral

section integral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma setIntegral_tilted' (f : α → ℝ) (g : α → E) {s : Set α} (hs : MeasurableSet s) :
    ∫ x in s, g x ∂(μ.tilted f) = ∫ x in s, (exp (f x) / ∫ x, exp (f x) ∂μ) • (g x) ∂μ := by
  by_cases hf : AEMeasurable f μ
  · rw [tilted_eq_withDensity_nnreal, setIntegral_withDensity_eq_setIntegral_smul₀ _ _ hs]
    · congr
    · suffices AEMeasurable (fun x ↦ exp (f x) / ∫ x, exp (f x) ∂μ) μ by
        rw [← aemeasurable_coe_nnreal_real_iff]
        refine AEMeasurable.restrict ?_
        simpa only [NNReal.coe_mk]
      exact (measurable_exp.comp_aemeasurable hf).div_const _
  · have hf' : ¬ Integrable (fun x ↦ exp (f x)) μ := by
      exact fun h ↦ hf (aemeasurable_of_aemeasurable_exp h.1.aemeasurable)
    simp only [hf, not_false_eq_true, tilted_of_not_aemeasurable, Measure.restrict_zero,
      integral_zero_measure]
    rw [integral_undef hf']
    simp

lemma setIntegral_tilted [SFinite μ] (f : α → ℝ) (g : α → E) (s : Set α) :
    ∫ x in s, g x ∂(μ.tilted f) = ∫ x in s, (exp (f x) / ∫ x, exp (f x) ∂μ) • (g x) ∂μ := by
  by_cases hf : AEMeasurable f μ
  · rw [tilted_eq_withDensity_nnreal, setIntegral_withDensity_eq_setIntegral_smul₀']
    · congr
    · suffices AEMeasurable (fun x ↦ exp (f x) / ∫ x, exp (f x) ∂μ) μ by
        rw [← aemeasurable_coe_nnreal_real_iff]
        refine AEMeasurable.restrict ?_
        simpa only [NNReal.coe_mk]
      exact (measurable_exp.comp_aemeasurable hf).div_const _
  · have hf' : ¬ Integrable (fun x ↦ exp (f x)) μ := by
      exact fun h ↦ hf (aemeasurable_of_aemeasurable_exp h.1.aemeasurable)
    simp only [hf, not_false_eq_true, tilted_of_not_aemeasurable, Measure.restrict_zero,
      integral_zero_measure]
    rw [integral_undef hf']
    simp

lemma integral_tilted (f : α → ℝ) (g : α → E) :
    ∫ x, g x ∂(μ.tilted f) = ∫ x, (exp (f x) / ∫ x, exp (f x) ∂μ) • (g x) ∂μ := by
  rw [← setIntegral_univ, setIntegral_tilted' f g MeasurableSet.univ, setIntegral_univ]

end integral

lemma integral_exp_tilted (f g : α → ℝ) :
    ∫ x, exp (g x) ∂(μ.tilted f) = (∫ x, exp ((f + g) x) ∂μ) / ∫ x, exp (f x) ∂μ := by
  cases eq_zero_or_neZero μ with
  | inl h => rw [h]; simp
  | inr h0 =>
    rw [integral_tilted f]
    simp_rw [smul_eq_mul]
    have : ∀ x, (exp (f x) / ∫ x, exp (f x) ∂μ) * exp (g x)
        = (exp ((f + g) x) / ∫ x, exp (f x) ∂μ) := by
      intro x
      rw [Pi.add_apply, exp_add]
      ring
    simp_rw [this, div_eq_mul_inv]
    rw [integral_mul_const]

lemma tilted_tilted (hf : Integrable (fun x ↦ exp (f x)) μ) (g : α → ℝ) :
    (μ.tilted f).tilted g = μ.tilted (f + g) := by
  cases eq_zero_or_neZero μ with
  | inl h => simp [h]
  | inr h0 =>
    ext1 s hs
    rw [tilted_apply' _ _ hs, tilted_apply' _ _ hs, setLIntegral_tilted' f _ hs]
    congr with x
    rw [← ENNReal.ofReal_mul (by positivity),
      integral_exp_tilted f, Pi.add_apply, exp_add]
    congr 1
    simp only [Pi.add_apply]
    have := (integral_exp_pos hf).ne'
    simp [field]

lemma tilted_comm (hf : Integrable (fun x ↦ exp (f x)) μ) {g : α → ℝ}
    (hg : Integrable (fun x ↦ exp (g x)) μ) :
    (μ.tilted f).tilted g = (μ.tilted g).tilted f := by
  rw [tilted_tilted hf, add_comm, tilted_tilted hg]

@[simp]
lemma tilted_neg_same' (hf : Integrable (fun x ↦ exp (f x)) μ) :
    (μ.tilted f).tilted (-f) = (μ Set.univ)⁻¹ • μ := by
  rw [tilted_tilted hf]; simp

lemma tilted_neg_same [IsProbabilityMeasure μ] (hf : Integrable (fun x ↦ exp (f x)) μ) :
    (μ.tilted f).tilted (-f) = μ := by
  simp [hf]

lemma tilted_absolutelyContinuous (μ : Measure α) (f : α → ℝ) : μ.tilted f ≪ μ :=
  withDensity_absolutelyContinuous _ _

lemma absolutelyContinuous_tilted (hf : Integrable (fun x ↦ exp (f x)) μ) : μ ≪ μ.tilted f := by
  cases eq_zero_or_neZero μ with
  | inl h => simp only [h, tilted_zero_measure]; exact fun _ _ ↦ by simp
  | inr h0 =>
    refine withDensity_absolutelyContinuous' ?_ ?_
    · exact (hf.1.aemeasurable.div_const _).ennreal_ofReal
    · filter_upwards
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact fun _ ↦ div_pos (exp_pos _) (integral_exp_pos hf)

lemma integrable_tilted_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : α → ℝ} (hf : Integrable (fun x ↦ exp (f x)) μ) (g : α → E) :
    Integrable g (μ.tilted f) ↔ Integrable (fun x ↦ exp (f x) • g x) μ := by
  by_cases hμ : μ = 0
  · simp [hμ]
  have hf_meas : AEMeasurable f μ := aemeasurable_of_aemeasurable_exp hf.1.aemeasurable
  rw [Measure.tilted, integrable_withDensity_iff_integrable_smul₀' (by fun_prop) (by simp)]
  calc Integrable (fun x ↦ (ENNReal.ofReal (exp (f x) / ∫ a, exp (f a) ∂μ)).toReal • g x) μ
  _ ↔ Integrable (fun x ↦ (exp (f x) / ∫ a, exp (f a) ∂μ) • g x) μ := by
    congr! with a
    rw [ENNReal.toReal_ofReal]
    positivity
  _ ↔ Integrable (fun x ↦ (∫ a, exp (f a) ∂μ)⁻¹ • exp (f x) • g x) μ := by
    congr! 2 with a
    rw [smul_smul, div_eq_inv_mul]
  _ ↔ Integrable (fun x ↦ exp (f x) • g x) μ := by
    rw [integrable_fun_smul_iff]
    simp only [ne_eq, inv_eq_zero]
    have : NeZero μ := ⟨hμ⟩
    exact (integral_exp_pos hf).ne'

lemma rnDeriv_tilted_right (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν]
    (hf : Integrable (fun x ↦ exp (f x)) ν) :
    μ.rnDeriv (ν.tilted f)
      =ᵐ[ν] fun x ↦ ENNReal.ofReal (exp (-f x) * ∫ x, exp (f x) ∂ν) * μ.rnDeriv ν x := by
  cases eq_zero_or_neZero ν with
  | inl h => simp_rw [h, ae_zero, Filter.EventuallyEq]; exact Filter.eventually_bot
  | inr h0 =>
    refine (Measure.rnDeriv_withDensity_right μ ν ?_ ?_ ?_).trans ?_
    · exact (hf.1.aemeasurable.div_const _).ennreal_ofReal
    · filter_upwards
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact fun _ ↦ div_pos (exp_pos _) (integral_exp_pos hf)
    · refine ae_of_all _ (by simp)
    · filter_upwards with x
      congr
      rw [← ENNReal.ofReal_inv_of_pos, inv_div', ← exp_neg, div_eq_mul_inv, inv_inv]
      exact div_pos (exp_pos _) (integral_exp_pos hf)

lemma toReal_rnDeriv_tilted_right (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν]
    (hf : Integrable (fun x ↦ exp (f x)) ν) :
    (fun x ↦ (μ.rnDeriv (ν.tilted f) x).toReal)
      =ᵐ[ν] fun x ↦ exp (-f x) * (∫ x, exp (f x) ∂ν) * (μ.rnDeriv ν x).toReal := by
  filter_upwards [rnDeriv_tilted_right μ ν hf] with x hx
  rw [hx]
  simp only [ENNReal.toReal_mul, mul_eq_mul_right_iff, ENNReal.toReal_ofReal_eq_iff]
  exact Or.inl (by positivity)

variable (μ) in
lemma rnDeriv_tilted_left {ν : Measure α} [SigmaFinite μ] [SigmaFinite ν] (hfν : AEMeasurable f ν) :
    (μ.tilted f).rnDeriv ν
      =ᵐ[ν] fun x ↦ ENNReal.ofReal (exp (f x) / (∫ x, exp (f x) ∂μ)) * μ.rnDeriv ν x := by
  let g := fun x ↦ ENNReal.ofReal (exp (f x) / (∫ x, exp (f x) ∂μ))
  refine Measure.rnDeriv_withDensity_left (μ := μ) (ν := ν) (f := g) ?_ ?_
  · exact ((measurable_exp.comp_aemeasurable hfν).div_const _).ennreal_ofReal
  · exact ae_of_all _ (fun x ↦ by simp [g])

variable (μ) in
lemma toReal_rnDeriv_tilted_left {ν : Measure α} [SigmaFinite μ] [SigmaFinite ν]
    (hfν : AEMeasurable f ν) :
    (fun x ↦ ((μ.tilted f).rnDeriv ν x).toReal)
      =ᵐ[ν] fun x ↦ exp (f x) / (∫ x, exp (f x) ∂μ) * (μ.rnDeriv ν x).toReal := by
  filter_upwards [rnDeriv_tilted_left μ hfν] with x hx
  rw [hx]
  simp only [ENNReal.toReal_mul, mul_eq_mul_right_iff, ENNReal.toReal_ofReal_eq_iff]
  exact Or.inl (by positivity)

lemma rnDeriv_tilted_left_self [SigmaFinite μ] (hf : AEMeasurable f μ) :
    (μ.tilted f).rnDeriv μ =ᵐ[μ] fun x ↦ ENNReal.ofReal (exp (f x) / ∫ x, exp (f x) ∂μ) := by
  refine (rnDeriv_tilted_left μ hf).trans ?_
  filter_upwards [Measure.rnDeriv_self μ] with x hx
  rw [hx, mul_one]

lemma log_rnDeriv_tilted_left_self [SigmaFinite μ] (hf : Integrable (fun x ↦ exp (f x)) μ) :
    (fun x ↦ log ((μ.tilted f).rnDeriv μ x).toReal)
      =ᵐ[μ] fun x ↦ f x - log (∫ x, exp (f x) ∂μ) := by
  cases eq_zero_or_neZero μ with
  | inl h => simp_rw [h, ae_zero, Filter.EventuallyEq]; exact Filter.eventually_bot
  | inr h0 =>
    have hf' : AEMeasurable f μ := aemeasurable_of_aemeasurable_exp hf.1.aemeasurable
    filter_upwards [rnDeriv_tilted_left_self hf'] with x hx
    rw [hx, ENNReal.toReal_ofReal (by positivity), log_div (exp_pos _).ne', log_exp]
    exact (integral_exp_pos hf).ne'

end MeasureTheory
