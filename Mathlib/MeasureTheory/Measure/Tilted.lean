/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Decomposition.RadonNikodym

/-!
# Exponentially tilted measures

The exponential tilting of a measure `μ` on `α` by a function `f : α → ℝ` is the measure with
density `x ↦ exp (f x - log ∫ x, exp (f x) ∂μ)` with respect to `μ`. This is sometimes also called
the Esscher transform, after F. Esscher who introduced it for `f` linear in
[esscher1932probability].

The definition is mostly used for `f` linear, in which case the exponentially tilted measure belongs
to the natural exponential family of the base measure. Exponentially tilted measures for general `f`
are used for example to establish variational expressions for the Kullback-Leibler divergence.

## Main definitions

* `logIntegralExp μ f`: the quantity `log (∫ x, exp (f x) ∂μ)`.
* `Measure.tilted μ f`: exponential tilting of `μ` by `f`, equal to
  `μ.withDensity (fun x ↦ ENNReal.ofReal (exp (f x - logIntegralExp μ f)))`.

-/

open Real

open scoped ENNReal NNReal

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α} {f : α → ℝ}

lemma aemeasurable_of_aemeasurable_exp (hf : AEMeasurable (fun x ↦ exp (f x)) μ) :
    AEMeasurable f μ := by
  have : f = fun x ↦ log (exp (f x)) := by ext; rw [log_exp]
  rw [this]
  exact measurable_log.comp_aemeasurable hf

lemma integral_exp_pos {μ : Measure α} {f : α → ℝ} [hμ : NeZero μ]
    (hf : Integrable (fun x ↦ exp (f x)) μ) :
    0 < ∫ x, exp (f x) ∂μ := by
  rw [integral_pos_iff_support_of_nonneg (fun x ↦ (exp_pos _).le) hf]
  suffices (Function.support fun x ↦ exp (f x)) = Set.univ by
    simp only [this, Measure.measure_univ_pos, ne_eq, hμ.out]
  ext1 x
  simp only [Function.mem_support, ne_eq, Set.mem_univ, iff_true]
  exact (exp_pos _).ne'

section logIntegralExp

/-- The quantity `log (∫ x, exp (f x) ∂μ)`. -/
noncomputable
def logIntegralExp (μ : Measure α) (f : α → ℝ) : ℝ := log (∫ x, exp (f x) ∂μ)

@[simp]
lemma logIntegralExp_zero_measure (f : α → ℝ) : logIntegralExp (0 : Measure α) f = 0 := by
  simp [logIntegralExp]

@[simp]
lemma logIntegralExp_zero (μ : Measure α) [IsProbabilityMeasure μ] : logIntegralExp μ 0 = 0 := by
  simp [logIntegralExp]

lemma logIntegralExp_of_not_integrable (hf : ¬ Integrable (fun x ↦ exp (f x)) μ) :
    logIntegralExp μ f = 0 := by
  simp only [logIntegralExp, log_eq_zero]
  exact Or.inl (integral_undef hf)

lemma exp_logIntegralExp [NeZero μ] (hf : Integrable (fun x ↦ exp (f x)) μ) :
    exp (logIntegralExp μ f) = ∫ x, exp (f x) ∂μ := by
  rw [logIntegralExp, exp_log (integral_exp_pos hf)]

end logIntegralExp

section tilted

/-- Exponentially tilted measure. `μ.tilted f` is the probability measure with density with respect
to `μ` proportional to `exp (f x)`. -/
noncomputable
def Measure.tilted (μ : Measure α) (f : α → ℝ) : Measure α :=
  μ.withDensity (fun x ↦ ENNReal.ofReal (exp (f x - logIntegralExp μ f)))

@[simp]
lemma tilted_zero_measure (f : α → ℝ) : (0 : Measure α).tilted f = 0 := by simp [Measure.tilted]

@[simp]
lemma tilted_const' (μ : Measure α) [IsFiniteMeasure μ] (c : ℝ) :
    μ.tilted (fun _ ↦ c) = (μ Set.univ)⁻¹ • μ := by
  cases eq_zero_or_neZero μ with
  | inl h => rw [h]; simp
  | inr h0 =>
    simp only [Measure.tilted, logIntegralExp, integral_const, smul_eq_mul]
    have h_pos : 0 < (μ Set.univ).toReal := by
      rw [ENNReal.toReal_pos_iff]
      simp [h0.out, measure_lt_top μ]
    rw [log_mul]
    · simp only [log_exp, sub_add_cancel'']
      rw [exp_neg, exp_log h_pos]
      have : (fun (_ : α) ↦ ENNReal.ofReal (ENNReal.toReal (μ Set.univ))⁻¹)
          = fun _ ↦ (μ Set.univ)⁻¹ := by
        ext1
        rw [← ENNReal.ofReal_inv_of_pos h_pos, ENNReal.ofReal_toReal]
        exact measure_ne_top _ _
      rw [this, withDensity_const]
    · rw [ENNReal.toReal_ne_zero, Measure.measure_univ_ne_zero]
      exact ⟨h0.out, measure_ne_top _ _⟩
    · exact (exp_pos _).ne'

lemma tilted_const (μ : Measure α) [IsProbabilityMeasure μ] (c : ℝ) :
    μ.tilted (fun _ ↦ c) = μ := by simp

@[simp]
lemma tilted_zero' (μ : Measure α) [IsFiniteMeasure μ] : μ.tilted 0 = (μ Set.univ)⁻¹ • μ := by
  change μ.tilted (fun _ ↦ 0) = (μ Set.univ)⁻¹ • μ
  simp

lemma tilted_zero (μ : Measure α) [IsProbabilityMeasure μ] : μ.tilted 0 = μ := by simp

lemma tilted_eq_withDensity_nnreal (μ : Measure α) (f : α → ℝ) :
    μ.tilted f = μ.withDensity
      (fun x ↦ ((↑) : ℝ≥0 → ℝ≥0∞) (⟨exp (f x - logIntegralExp μ f), (exp_pos _).le⟩ : ℝ≥0)) := by
  rw [Measure.tilted]
  congr with x
  rw [ENNReal.ofReal_eq_coe_nnreal]

lemma tilted_apply (μ : Measure α) (f : α → ℝ) {s : Set α} (hs : MeasurableSet s) :
    μ.tilted f s = ∫⁻ a in s, ENNReal.ofReal (exp (f a - logIntegralExp μ f)) ∂μ := by
  rw [Measure.tilted, withDensity_apply _ hs]

lemma tilted_apply_eq_ofReal_integral (hf : Integrable (fun x ↦ exp (f x)) μ)
    {s : Set α} (hs : MeasurableSet s) :
    μ.tilted f s = ENNReal.ofReal (∫ a in s, exp (f a - logIntegralExp μ f) ∂μ) := by
  rw [tilted_apply _ _ hs, ← ofReal_integral_eq_lintegral_ofReal]
  · simp_rw [exp_sub, div_eq_mul_inv]
    refine Integrable.integrableOn ?_
    exact hf.mul_const _
  · exact ae_of_all _ (fun x ↦ (exp_pos _).le)

lemma sigmaFinite_tilted [SigmaFinite μ] (hf : AEMeasurable f μ) : SigmaFinite (μ.tilted f) :=
  SigmaFinite.withDensity_ofReal (measurable_exp.comp_aemeasurable (hf.sub aemeasurable_const))

lemma isFiniteMeasure_tilted (hf : Integrable (fun x ↦ exp (f x)) μ) :
    IsFiniteMeasure (μ.tilted f) := by
  refine isFiniteMeasure_withDensity_ofReal ?_
  suffices Integrable (fun x ↦ exp (f x - logIntegralExp μ f)) μ by exact this.2
  simp_rw [exp_sub]
  exact hf.div_const _

lemma isProbabilityMeasure_tilted [NeZero μ] (hf : Integrable (fun x ↦ exp (f x)) μ) :
    IsProbabilityMeasure (μ.tilted f) := by
  constructor
  simp_rw [tilted_apply _ _ MeasurableSet.univ, set_lintegral_univ, exp_sub,
    ENNReal.ofReal_div_of_pos (exp_pos _), div_eq_mul_inv]
  have h_ne_top : (ENNReal.ofReal (rexp (logIntegralExp μ f)))⁻¹ ≠ ⊤ := by simp [exp_pos]
  rw [lintegral_mul_const' _ _ h_ne_top]
  rw [exp_logIntegralExp hf, ← ofReal_integral_eq_lintegral_ofReal hf]
  · rw [ENNReal.mul_inv_cancel]
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    · exact integral_exp_pos hf
    · simp
  · exact ae_of_all _ fun _ ↦ (exp_pos _).le

section Integrals

lemma set_lintegral_tilted (hf : AEMeasurable f μ) (g : α → ℝ≥0∞)
    {s : Set α} (hs : MeasurableSet s) :
    ∫⁻ x in s, g x ∂(μ.tilted f)
      = ∫⁻ x in s, ENNReal.ofReal (exp (f x - logIntegralExp μ f)) * g x ∂μ := by
  rw [Measure.tilted, set_lintegral_withDensity_eq_set_lintegral_mul_non_measurable₀]
  · simp only [Pi.mul_apply]
  · refine AEMeasurable.restrict ?_
    exact measurable_exp.ennreal_ofReal.comp_aemeasurable (hf.sub aemeasurable_const)
  · exact hs
  · refine ae_of_all _ ?_
    simp only [ENNReal.ofReal_lt_top, implies_true]

lemma lintegral_tilted (hf : AEMeasurable f μ) (g : α → ℝ≥0∞) :
    ∫⁻ x, g x ∂(μ.tilted f) = ∫⁻ x, ENNReal.ofReal (exp (f x - logIntegralExp μ f)) * (g x) ∂μ := by
  rw [← set_lintegral_univ, set_lintegral_tilted hf g MeasurableSet.univ, set_lintegral_univ]

lemma set_integral_tilted {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hf : AEMeasurable f μ) (g : α → E) {s : Set α} (hs : MeasurableSet s) :
    ∫ x in s, g x ∂(μ.tilted f) = ∫ x in s, exp (f x - logIntegralExp μ f) • (g x) ∂μ := by
  rw [tilted_eq_withDensity_nnreal, set_integral_withDensity_eq_set_integral_smul₀ _ _ hs]
  · congr
  · suffices AEMeasurable (fun x ↦ exp (f x - logIntegralExp μ f)) μ by
      rw [← aEMeasurable_coe_nnreal_real_iff]
      refine AEMeasurable.restrict ?_
      simpa only [NNReal.coe_mk]
    exact measurable_exp.comp_aemeasurable (hf.sub aemeasurable_const)

lemma integral_tilted {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hf : AEMeasurable f μ) (g : α → E) :
    ∫ x, g x ∂(μ.tilted f) = ∫ x, exp (f x - logIntegralExp μ f) • (g x) ∂μ := by
  rw [← integral_univ, set_integral_tilted hf g MeasurableSet.univ, integral_univ]

end Integrals

lemma logIntegralExp_tilted {g : α → ℝ} (hf : AEMeasurable f μ)
    (hfg : Integrable (fun x ↦ exp ((f + g) x)) μ) :
    logIntegralExp (μ.tilted f) g = logIntegralExp μ (f + g) - logIntegralExp μ f := by
  cases eq_zero_or_neZero μ with
  | inl h => rw [h]; simp
  | inr h0 =>
    rw [logIntegralExp, integral_tilted hf]
    simp_rw [smul_eq_mul, ← exp_add]
    have : (fun x ↦ exp (f x - logIntegralExp μ f + g x))
        = fun x ↦ exp ((f + g) x) * exp (- logIntegralExp μ f) := by
      ext x
      rw [Pi.add_apply, ← exp_add]
      congr 1
      abel
    simp_rw [this]
    rw [integral_mul_right, log_mul (integral_exp_pos hfg).ne' (exp_pos _).ne', log_exp,
      ← sub_eq_add_neg]
    rfl

lemma tilted_tilted {g : α → ℝ} (hf : AEMeasurable f μ)
    (hfg : Integrable (fun x ↦ exp ((f + g) x)) μ) :
    (μ.tilted f).tilted g = μ.tilted (f + g) := by
  cases eq_zero_or_neZero μ with
  | inl h => simp [h]
  | inr h0 =>
    ext1 s hs
    rw [tilted_apply _ _ hs, tilted_apply _ _ hs, set_lintegral_tilted hf _ hs]
    congr with x
    rw [← ENNReal.ofReal_mul (exp_pos _).le, ← exp_add, logIntegralExp_tilted hf hfg, Pi.add_apply]
    congr 2
    abel

@[simp]
lemma tilted_neg_same' [IsFiniteMeasure μ] (hf : AEMeasurable f μ) :
    (μ.tilted f).tilted (-f) = (μ Set.univ)⁻¹ • μ := by
  rw [tilted_tilted hf] <;> simp

@[simp]
lemma tilted_neg_same [IsProbabilityMeasure μ] (hf : AEMeasurable f μ) :
    (μ.tilted f).tilted (-f) = μ := by
  simp [hf]

lemma tilted_absolutelyContinuous (μ : Measure α) (f : α → ℝ) : μ.tilted f ≪ μ :=
  withDensity_absolutelyContinuous _ _

lemma absolutelyContinuous_tilted (hf : AEMeasurable f μ) : μ ≪ μ.tilted f := by
  refine withDensity_absolutelyContinuous' ?_ ?_ ?_
  · exact measurable_exp.ennreal_ofReal.comp_aemeasurable (hf.sub aemeasurable_const)
  · refine ae_of_all _ ?_
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact fun _ ↦ exp_pos _
  · refine ae_of_all _ (by simp)

lemma rnDeriv_tilted_right (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν]
    (hf : AEMeasurable f ν) :
    μ.rnDeriv (ν.tilted f)
      =ᵐ[ν] fun x ↦ ENNReal.ofReal (exp (- f x + logIntegralExp ν f)) * μ.rnDeriv ν x := by
  refine (Measure.rnDeriv_withDensity_right μ ν ?_ ?_ ?_).trans ?_
  · exact measurable_exp.ennreal_ofReal.comp_aemeasurable (hf.sub aemeasurable_const)
  · refine ae_of_all _ ?_
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact fun _ ↦ exp_pos _
  · refine ae_of_all _ (by simp)
  · refine ae_of_all _ (fun x ↦ ?_)
    simp only
    congr
    rw [ENNReal.ofReal_inv_of_pos (exp_pos _), ← exp_neg]
    congr
    abel

lemma ofReal_rnDeriv_tilted_right (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν]
    (hf : AEMeasurable f ν) :
    (fun x ↦ (μ.rnDeriv (ν.tilted f) x).toReal)
      =ᵐ[ν] fun x ↦ exp (- f x + logIntegralExp ν f) * (μ.rnDeriv ν x).toReal := by
  filter_upwards [rnDeriv_tilted_right μ ν hf] with x hx
  rw [hx]
  simp only [ENNReal.toReal_mul, mul_eq_mul_right_iff, ENNReal.toReal_ofReal_eq_iff]
  exact Or.inl (exp_pos _).le

lemma rnDeriv_tilted_left {ν : Measure α} [SigmaFinite μ] [SigmaFinite ν]
    (hfμ : AEMeasurable f μ) (hfν : AEMeasurable f ν) :
    (μ.tilted f).rnDeriv ν
      =ᵐ[ν] fun x ↦ ENNReal.ofReal (exp (f x - logIntegralExp μ f)) * μ.rnDeriv ν x := by
  let g := fun x ↦ ENNReal.ofReal (exp (f x - logIntegralExp μ f))
  refine Measure.rnDeriv_withDensity_left (μ := μ) (ν := ν) (f := g) ?_ ?_ ?_
  · exact measurable_exp.ennreal_ofReal.comp_aemeasurable (hfμ.sub aemeasurable_const)
  · exact measurable_exp.ennreal_ofReal.comp_aemeasurable (hfν.sub aemeasurable_const)
  · exact ae_of_all _ (fun x ↦ by simp)

lemma ofReal_rnDeriv_tilted_left {ν : Measure α} [SigmaFinite μ] [SigmaFinite ν]
    (hfμ : AEMeasurable f μ) (hfν : AEMeasurable f ν) :
    (fun x ↦ ((μ.tilted f).rnDeriv ν x).toReal)
      =ᵐ[ν] fun x ↦ exp (f x - logIntegralExp μ f) * (μ.rnDeriv ν x).toReal := by
  filter_upwards [rnDeriv_tilted_left hfμ hfν] with x hx
  rw [hx]
  simp only [ENNReal.toReal_mul, mul_eq_mul_right_iff, ENNReal.toReal_ofReal_eq_iff]
  exact Or.inl (exp_pos _).le

lemma rnDeriv_tilted_left_self [SigmaFinite μ] (hf : AEMeasurable f μ) :
    (μ.tilted f).rnDeriv μ =ᵐ[μ] fun x ↦ ENNReal.ofReal (exp (f x - logIntegralExp μ f)) := by
  refine (rnDeriv_tilted_left hf hf).trans ?_
  filter_upwards [Measure.rnDeriv_self μ] with x hx using by rw [hx, mul_one]

lemma log_rnDeriv_tilted_left_self [SigmaFinite μ] (hf : AEMeasurable f μ) :
    (fun x ↦ log ((μ.tilted f).rnDeriv μ x).toReal) =ᵐ[μ] fun x ↦ f x - logIntegralExp μ f := by
  filter_upwards [rnDeriv_tilted_left_self hf] with x hx
  rw [hx, ENNReal.toReal_ofReal (exp_pos _).le, log_exp]

end tilted

end MeasureTheory
