/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Decomposition.RadonNikodym

/-!
# Exponentially tilted measures

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

## References

TODO: cite Esscher 1932

* [F. Bar, *Quuxes*][bibkey]

-/

open Real

open scoped ENNReal NNReal

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α}

lemma aemeasurable_of_aemeasurable_exp {μ : Measure α} {f : α → ℝ}
    (hf : AEMeasurable (fun x ↦ exp (f x)) μ) :
    AEMeasurable f μ := by
  have : f = fun x ↦ log (exp (f x)) := by ext; rw [log_exp]
  rw [this]
  exact measurable_log.comp_aemeasurable hf

lemma integral_exp_pos {μ : Measure α} {f : α → ℝ} [hμ : NeZero μ]
    (hf : Integrable (fun x ↦ exp (f x)) μ) :
    0 < ∫ x, exp (f x) ∂μ := by
  rw [integral_pos_iff_support_of_nonneg]
  · suffices (Function.support fun x ↦ exp (f x)) = Set.univ by
      rw [this]
      simp only [Measure.measure_univ_pos, ne_eq]
      exact hμ.out
    ext1 x
    simp only [Function.mem_support, ne_eq, Set.mem_univ, iff_true]
    exact (exp_pos _).ne'
  · exact fun x ↦ (exp_pos _).le
  · exact hf

section tilted

noncomputable
def logIntegralExp (μ : Measure α) (f : α → ℝ) : ℝ := log (∫ x, exp (f x) ∂μ)

@[simp]
lemma logIntegralExp_zero_left (f : α → ℝ) :
    logIntegralExp (0 : Measure α) f = 0 := by
  simp [logIntegralExp]

@[simp]
lemma logIntegralExp_zero_right (μ : Measure α) [IsProbabilityMeasure μ] :
    logIntegralExp μ 0 = 0 := by
  simp [logIntegralExp]

lemma logIntegralExp_of_not_integrable {μ : Measure α} {f : α → ℝ}
    (hf : ¬ Integrable (fun x ↦ exp (f x)) μ) :
    logIntegralExp μ f = 0 := by
  simp only [logIntegralExp, log_eq_zero]
  exact Or.inl (integral_undef hf)

lemma exp_logIntegralExp {μ : Measure α} [NeZero μ] {f : α → ℝ}
    (hf : Integrable (fun x ↦ exp (f x)) μ) :
    exp (logIntegralExp μ f) = ∫ x, exp (f x) ∂μ := by
  rw [logIntegralExp, exp_log]
  exact integral_exp_pos hf

noncomputable
def Measure.tilted (μ : Measure α) (f : α → ℝ) : Measure α :=
  μ.withDensity (fun x ↦ ENNReal.ofReal (exp (f x - logIntegralExp μ f)))

lemma tilted_absolutelyContinuous {μ : Measure α} {f : α → ℝ} : μ.tilted f ≪ μ :=
  withDensity_absolutelyContinuous _ _

@[simp]
lemma tilted_zero_left (f : α → ℝ) : (0 : Measure α).tilted f = 0 := by
  simp [Measure.tilted]

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
    μ.tilted (fun _ ↦ c) = μ := by
  simp

@[simp]
lemma tilted_zero' (μ : Measure α) [IsFiniteMeasure μ] : μ.tilted 0 = (μ Set.univ)⁻¹ • μ := by
  change μ.tilted (fun _ ↦ 0) = (μ Set.univ)⁻¹ • μ
  simp

lemma tilted_zero (μ : Measure α) [IsProbabilityMeasure μ] : μ.tilted 0 = μ := by simp

lemma tilted_eq_withDensity_nnreal (μ : Measure α) (f : α → ℝ) :
    μ.tilted f = μ.withDensity
      (fun x ↦ ((↑) : ℝ≥0 → ℝ≥0∞) (⟨exp (f x - logIntegralExp μ f), (exp_pos _).le⟩ : ℝ≥0)) := by
  rw [Measure.tilted]
  congr
  ext1 x
  rw [ENNReal.ofReal_eq_coe_nnreal]

lemma tilted_apply (μ : Measure α) (f : α → ℝ) {s : Set α} (hs : MeasurableSet s) :
    μ.tilted f s = ∫⁻ a in s, ENNReal.ofReal (exp (f a - logIntegralExp μ f)) ∂μ := by
  rw [Measure.tilted, withDensity_apply _ hs]

lemma tilted_apply_eq_ofReal_integral (μ : Measure α)
    {f : α → ℝ} (hf : Integrable (fun x ↦ exp (f x)) μ)
    {s : Set α} (hs : MeasurableSet s) :
    μ.tilted f s = ENNReal.ofReal (∫ a in s, exp (f a - logIntegralExp μ f) ∂μ) := by
  rw [tilted_apply _ _ hs, ← ofReal_integral_eq_lintegral_ofReal]
  · simp_rw [exp_sub, div_eq_mul_inv]
    refine Integrable.integrableOn ?_
    exact hf.mul_const _
  · exact ae_of_all _ (fun x ↦ (exp_pos _).le)

lemma set_lintegral_tilted {μ : Measure α} {f : α → ℝ} (hf : AEMeasurable f μ) (g : α → ℝ≥0∞)
    {s : Set α} (hs : MeasurableSet s) :
    ∫⁻ x in s, g x ∂(μ.tilted f)
      = ∫⁻ x in s, ENNReal.ofReal (exp (f x - logIntegralExp μ f)) * (g x) ∂μ := by
  rw [Measure.tilted, set_lintegral_withDensity_eq_set_lintegral_mul_non_measurable₀]
  · simp only [Pi.mul_apply]
  · refine AEMeasurable.restrict ?_
    refine ENNReal.measurable_ofReal.comp_aemeasurable ?_
    exact measurable_exp.comp_aemeasurable (hf.sub aemeasurable_const)
  · exact hs
  · refine ae_of_all _ ?_
    simp only [ENNReal.ofReal_lt_top, implies_true]

lemma lintegral_tilted {μ : Measure α} {f : α → ℝ} (hf : AEMeasurable f μ) (g : α → ℝ≥0∞) :
    ∫⁻ x, g x ∂(μ.tilted f) = ∫⁻ x, ENNReal.ofReal (exp (f x - logIntegralExp μ f)) * (g x) ∂μ := by
  rw [← set_lintegral_univ, set_lintegral_tilted hf g MeasurableSet.univ, set_lintegral_univ]

lemma set_integral_tilted {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {μ : Measure α} {f : α → ℝ} (hf : AEMeasurable f μ) (g : α → E)
    {s : Set α} (hs : MeasurableSet s) :
    ∫ x in s, g x ∂(μ.tilted f) = ∫ x in s, exp (f x - logIntegralExp μ f) • (g x) ∂μ := by
  rw [tilted_eq_withDensity_nnreal, set_integral_withDensity_eq_set_integral_smul₀ _ _ hs]
  · congr
  · suffices AEMeasurable (fun x ↦ exp (f x - logIntegralExp μ f)) μ by
      rw [← aEMeasurable_coe_nnreal_real_iff]
      refine AEMeasurable.restrict ?_
      simpa only [NNReal.coe_mk]
    exact measurable_exp.comp_aemeasurable (hf.sub aemeasurable_const)

lemma integral_tilted {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {μ : Measure α} {f : α → ℝ} (hf : AEMeasurable f μ) (g : α → E) :
    ∫ x, g x ∂(μ.tilted f) = ∫ x, exp (f x - logIntegralExp μ f) • (g x) ∂μ := by
  rw [← integral_univ, set_integral_tilted hf g MeasurableSet.univ, integral_univ]

lemma isFiniteMeasure_tilted {μ : Measure α} {f : α → ℝ}
    (hf : Integrable (fun x ↦ exp (f x)) μ) :
    IsFiniteMeasure (μ.tilted f) := by
  constructor
  simp_rw [tilted_apply _ _ MeasurableSet.univ, set_lintegral_univ, exp_sub,
    ENNReal.ofReal_div_of_pos (exp_pos _), div_eq_mul_inv]
  have h_ne_top : (ENNReal.ofReal (rexp (logIntegralExp μ f)))⁻¹ ≠ ⊤ := by simp [exp_pos]
  rw [lintegral_mul_const' _ _ h_ne_top]
  refine ENNReal.mul_lt_top ?_ h_ne_top
  rw [← ofReal_integral_eq_lintegral_ofReal hf]
  · simp only [ne_eq, ENNReal.ofReal_ne_top, not_false_eq_true]
  · exact ae_of_all _ fun _ ↦ (exp_pos _).le

lemma isProbabilityMeasure_tilted {μ : Measure α} [NeZero μ] {f : α → ℝ}
    (hf : Integrable (fun x ↦ exp (f x)) μ) :
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

lemma logIntegralExp_tilted {μ : Measure α} {f g : α → ℝ} (hf : AEMeasurable f μ)
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

lemma tilted_tilted {μ : Measure α} {f g : α → ℝ} (hf : AEMeasurable f μ)
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
lemma tilted_inv_same' {μ : Measure α} [IsFiniteMeasure μ] {f : α → ℝ} (hf : AEMeasurable f μ) :
    (μ.tilted f).tilted (-f) = (μ Set.univ)⁻¹ • μ := by
  rw [tilted_tilted hf] <;> simp

@[simp]
lemma tilted_inv_same {μ : Measure α} [IsProbabilityMeasure μ] {f : α → ℝ} (hf : AEMeasurable f μ) :
    (μ.tilted f).tilted (-f) = μ := by
  simp [hf]

lemma Measure.AbsolutelyContinuous.zero (μ : Measure α) : 0 ≪ μ := fun s _ ↦ by simp

lemma absolutelyContinuous_tilted {μ : Measure α} [IsFiniteMeasure μ] {f : α → ℝ}
    (hf : AEMeasurable f μ) :
    μ ≪ μ.tilted f := by
  cases eq_zero_or_neZero μ with
  | inl h => rw [h]; exact Measure.AbsolutelyContinuous.zero _
  | inr h0 =>
    have : μ = (μ Set.univ) • (μ.tilted f).tilted (-f) := by
      rw [tilted_inv_same' hf]
      rw [smul_smul, ENNReal.mul_inv_cancel, one_smul]
      · simp [h0.out]
      · exact measure_ne_top _ _
    nth_rw 1 [this]
    exact tilted_absolutelyContinuous.smul (μ Set.univ)

lemma rnDeriv_tilted_left_self (μ : Measure α) [SigmaFinite μ] {f : α → ℝ} (hf : Measurable f) :
    (μ.tilted f).rnDeriv μ =ᵐ[μ] fun x ↦ ENNReal.ofReal (exp (f x - logIntegralExp μ f)) :=
  Measure.rnDeriv_withDensity μ (hf.sub measurable_const).exp.ennreal_ofReal

lemma log_rnDeriv_tilted_left_self (μ : Measure α) [SigmaFinite μ] {f : α → ℝ} (hf : Measurable f) :
    (fun x ↦ log ((μ.tilted f).rnDeriv μ x).toReal)
      =ᵐ[μ] fun x ↦ f x - logIntegralExp μ f := by
  filter_upwards [rnDeriv_tilted_left_self μ hf] with x hx
  rw [hx, ENNReal.toReal_ofReal (exp_pos _).le, log_exp]

lemma rnDeriv_tilted_right_of_absolutelyContinuous (μ ν : Measure α) [SigmaFinite μ]
    [IsFiniteMeasure ν] (hμν : μ ≪ ν)
    {f : α → ℝ} (hf : AEMeasurable f ν) (h_int : Integrable (fun x ↦ exp (f x)) ν) :
    (fun x ↦ (μ.rnDeriv (ν.tilted f) x).toReal)
      =ᵐ[ν] fun x ↦ exp (- f x + logIntegralExp ν f) * (μ.rnDeriv ν x).toReal := by
  cases eq_zero_or_neZero ν with
  | inl h => simp only [h, ae_zero]; exact Filter.eventually_bot
  | inr h0 =>
    suffices μ.rnDeriv (ν.tilted f)
        =ᵐ[ν] fun x ↦ (ENNReal.ofReal (exp (- f x + logIntegralExp ν f)) * μ.rnDeriv ν x) by
      suffices (fun x ↦ (μ.rnDeriv (ν.tilted f) x).toReal) =ᵐ[ν]
          fun x ↦ (ENNReal.ofReal (exp (- f x + logIntegralExp ν f)) * μ.rnDeriv ν x).toReal by
        filter_upwards [this] with x hx
        rw [hx, ENNReal.toReal_mul, ENNReal.toReal_ofReal (exp_pos _).le]
      filter_upwards [this] with x hx
      rw [hx]
    symm
    refine (absolutelyContinuous_tilted hf).ae_le ?_
    have : IsProbabilityMeasure (ν.tilted f) := isProbabilityMeasure_tilted h_int
    refine Measure.eq_rnDeriv₀ ?_ Measure.MutuallySingular.zero_left ?_
    · simp only
      refine AEMeasurable.mul ?_ (Measure.measurable_rnDeriv _ _).aemeasurable
      refine ENNReal.measurable_ofReal.comp_aemeasurable ?_
      refine measurable_exp.comp_aemeasurable ((AEMeasurable.neg ?_).add aemeasurable_const)
      exact AEMeasurable.mono_ac hf tilted_absolutelyContinuous
    · ext1 s hs
      conv_lhs => rw [← Measure.withDensity_rnDeriv_eq _ _ hμν]
      rw [zero_add]
      simp only [Measure.add_toOuterMeasure, OuterMeasure.coe_add, Pi.add_apply]
      rw [withDensity_apply _ hs, withDensity_apply _ hs, set_lintegral_tilted hf _ hs]
      simp_rw [← mul_assoc, ← ENNReal.ofReal_mul (exp_pos _).le, ← exp_add]
      congr with x
      simp only [sub_add_add_cancel, add_right_neg, exp_zero, ENNReal.ofReal_one, one_mul]

lemma rnDeriv_tilted_right (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {f : α → ℝ} (hf : AEMeasurable f ν) (h_int : Integrable (fun x ↦ exp (f x)) ν) :
    (fun x ↦ (μ.rnDeriv (ν.tilted f) x).toReal)
      =ᵐ[ν] fun x ↦ exp (- f x + logIntegralExp ν f) * (μ.rnDeriv ν x).toReal := by
  cases eq_zero_or_neZero ν with
  | inl h => simp only [h, ae_zero]; exact Filter.eventually_bot
  | inr h0 =>
    have : IsProbabilityMeasure (ν.tilted f) := isProbabilityMeasure_tilted h_int
    let μ' := ν.withDensity (μ.rnDeriv ν)
    have h₁ : μ.rnDeriv (ν.tilted f) =ᵐ[ν] μ'.rnDeriv (ν.tilted f) := by
      conv_lhs => rw [μ.haveLebesgueDecomposition_add ν]
      have hν_ac : ν ≪ ν.tilted f := absolutelyContinuous_tilted hf
      have h_add : (μ.singularPart ν + ν.withDensity (μ.rnDeriv ν)).rnDeriv (ν.tilted f)
          =ᵐ[ν] (μ.singularPart ν).rnDeriv (ν.tilted f) + _ :=
        hν_ac.ae_le (Measure.rnDeriv_add (μ.singularPart ν) μ' (ν.tilted f))
      refine h_add.trans ?_
      suffices (μ.singularPart ν).rnDeriv (ν.tilted f) =ᵐ[ν] 0 by
        filter_upwards [this] with x hx
        rw [Pi.add_apply, hx, Pi.zero_apply, zero_add]
      refine hν_ac.ae_le ?_
      refine Measure.MutuallySingular.rnDeriv_ae_eq_zero ?_
      exact Measure.MutuallySingular.mono_ac (μ.mutuallySingular_singularPart ν)
        Measure.AbsolutelyContinuous.rfl tilted_absolutelyContinuous
    have h₂ : μ.rnDeriv ν =ᵐ[ν] μ'.rnDeriv ν :=
      (Measure.rnDeriv_withDensity _ (Measure.measurable_rnDeriv _ _)).symm
    have hμ' := rnDeriv_tilted_right_of_absolutelyContinuous μ' ν
      (withDensity_absolutelyContinuous ν _) hf h_int
    filter_upwards [h₁, h₂, hμ'] with x hx₁ hx₂ hx_eq
    rw [hx₁, hx₂, hx_eq]

end tilted

end MeasureTheory
