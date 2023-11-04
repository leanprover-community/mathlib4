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

lemma Measure.AbsolutelyContinuous.zero (μ : Measure α) : 0 ≪ μ := fun s _ ↦ by simp

lemma _root_.AEMeasurable.singularPart {β : Type*} {_ : MeasurableSpace β} {f : α → β}
    (hf : AEMeasurable f μ) (ν : Measure α) :
    AEMeasurable f (μ.singularPart ν) :=
  AEMeasurable.mono_measure hf (Measure.singularPart_le _ _)

lemma _root_.AEMeasurable.withDensity_rnDeriv {β : Type*} {_ : MeasurableSpace β} {f : α → β}
    (hf : AEMeasurable f μ) (ν : Measure α) :
    AEMeasurable f (ν.withDensity (μ.rnDeriv ν)) :=
  AEMeasurable.mono_measure hf (Measure.withDensity_rnDeriv_le _ _)

lemma aemeasurable_of_aemeasurable_exp (hf : AEMeasurable (fun x ↦ exp (f x)) μ) :
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

lemma rnDeriv_mul_rnDeriv {μ ν κ : Measure α} [SigmaFinite κ]
    [μ.HaveLebesgueDecomposition κ] [ν.HaveLebesgueDecomposition κ] [μ.HaveLebesgueDecomposition ν]
    (hμν : μ ≪ ν) (hνκ : ν ≪ κ) :
    μ.rnDeriv ν * ν.rnDeriv κ =ᵐ[κ] μ.rnDeriv κ := by
  rw [← withDensity_eq_iff_of_sigmaFinite]
  · rw [mul_comm,
      withDensity_mul _ (Measure.measurable_rnDeriv _ _) (Measure.measurable_rnDeriv _ _),
      Measure.withDensity_rnDeriv_eq _ _ (hμν.trans hνκ), Measure.withDensity_rnDeriv_eq _ _ hνκ,
      Measure.withDensity_rnDeriv_eq _ _ hμν]
  · exact ((Measure.measurable_rnDeriv _ _).mul (Measure.measurable_rnDeriv _ _)).aemeasurable
  · exact (Measure.measurable_rnDeriv _ _).aemeasurable

lemma StronglyMeasurable.exists_spanning_measurableSet_norm_le'
    {β : Type*} [SeminormedAddCommGroup β] {f : α → β}
    (hf : StronglyMeasurable f) (μ : Measure α) [SigmaFinite μ] :
    ∃ s : ℕ → Set α, (∀ n, MeasurableSet (s n) ∧ μ (s n) < ∞ ∧ ∀ x ∈ s n, ‖f x‖ ≤ n) ∧
      ⋃ i, s i = Set.univ := by
  have : SigmaFinite (Measure.trim μ le_rfl) := by rw [trim_eq_self]; infer_instance
  exact StronglyMeasurable.exists_spanning_measurableSet_norm_le le_rfl hf μ

section withDensity

lemma Measure.withDensity.sigmaFinite_ofReal_of_stronglyMeasurable [SigmaFinite μ] {f : α → ℝ}
    (hf : StronglyMeasurable f) :
    SigmaFinite (μ.withDensity (fun x ↦ ENNReal.ofReal (f x))) := by
  obtain ⟨s, hs, h⟩ := StronglyMeasurable.exists_spanning_measurableSet_norm_le' hf μ
  constructor
  refine ⟨s, by simp, fun i ↦ ?_, h⟩
  rw [withDensity_apply _ (hs i).1]
  calc ∫⁻ a in s i, ENNReal.ofReal (f a) ∂μ
    ≤ ∫⁻ _ in s i, i ∂μ := by
        refine set_lintegral_mono hf.measurable.ennreal_ofReal measurable_const (fun x hxs ↦ ?_)
        refine (ofReal_le_ennnorm _).trans ?_
        rw [← ofReal_norm_eq_coe_nnnorm]
        refine ENNReal.ofReal_le_of_le_toReal ?_
        simp only [ENNReal.toReal_nat]
        exact (hs i).2.2 x hxs
  _ = i * μ (s i) := by rw [set_lintegral_const]
  _ < ⊤ := ENNReal.mul_lt_top (by simp) (hs i).2.1.ne

lemma Measure.withDensity.sigmaFinite_ofReal [SigmaFinite μ] {f : α → ℝ}
    (hf : AEStronglyMeasurable f μ) :
    SigmaFinite (μ.withDensity (fun x ↦ ENNReal.ofReal (f x))) := by
  have h : (fun x ↦ ENNReal.ofReal (f x)) =ᵐ[μ] fun x ↦ ENNReal.ofReal (hf.mk f x) := by
    filter_upwards [hf.ae_eq_mk] with x hx using by rw [hx]
  rw [withDensity_congr_ae h]
  exact Measure.withDensity.sigmaFinite_ofReal_of_stronglyMeasurable hf.stronglyMeasurable_mk

instance Measure.withDensity.sigmaFinite [SigmaFinite μ] {f : α → ℝ≥0}
    (hf : AEMeasurable f μ) :
    SigmaFinite (μ.withDensity (fun x ↦ f x)) := by
  have : (fun x ↦ (f x : ℝ≥0∞)) = fun x ↦ ENNReal.ofReal (f x) := by simp
  rw [this]
  exact Measure.withDensity.sigmaFinite_ofReal hf.coe_nnreal_real.aestronglyMeasurable

lemma Measure.withDensity.sigmaFinite_of_ne_top' [SigmaFinite μ] {f : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) (hf_ne_top : ∀ x, f x ≠ ∞) :
    SigmaFinite (μ.withDensity f) := by
  lift f to (α → ℝ≥0) using hf_ne_top
  rw [aemeasurable_coe_nnreal_ennreal_iff] at hf
  exact Measure.withDensity.sigmaFinite hf

lemma Measure.withDensity.sigmaFinite_of_ne_top [SigmaFinite μ] {f : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) (hf_ne_top : ∀ᵐ x ∂μ, f x ≠ ∞) :
    SigmaFinite (μ.withDensity f) := by
  let f' := fun x ↦ if f x = ∞ then 0 else f x
  have hff' : f =ᵐ[μ] f' := by filter_upwards [hf_ne_top] with x hx using by simp [hx]
  have hf'_ne_top : ∀ x, f' x ≠ ∞ := fun x ↦ by by_cases hfx : f x = ∞ <;> simp [hfx]
  rw [withDensity_congr_ae hff']
  exact Measure.withDensity.sigmaFinite_of_ne_top' (hf.congr hff') hf'_ne_top

lemma Measure.MutuallySingular.withDensity {ν : Measure α} {f : α → ℝ≥0∞} (h : μ ⟂ₘ ν) :
    μ.withDensity f ⟂ₘ ν :=
  MutuallySingular.mono_ac h (withDensity_absolutelyContinuous _ _) AbsolutelyContinuous.rfl

lemma todo_left (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν]
    {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) (hf_ne_top : ∀ᵐ x ∂μ, f x ≠ ∞) :
    ((ν.withDensity (μ.rnDeriv ν)).withDensity f).rnDeriv ν =ᵐ[ν] (μ.withDensity f).rnDeriv ν := by
  let μ' := ν.withDensity (μ.rnDeriv ν)
  change (μ'.withDensity f).rnDeriv ν =ᵐ[ν] (μ.withDensity f).rnDeriv ν
  rw [μ.haveLebesgueDecomposition_add ν, withDensity_add_measure]
  have : SigmaFinite ((μ.singularPart ν).withDensity f) := by
    refine Measure.withDensity.sigmaFinite_of_ne_top ?_ ?_
    · exact hf.singularPart ν
    · exact (Measure.absolutelyContinuous_of_le (Measure.singularPart_le _ _)).ae_le hf_ne_top
  have : SigmaFinite (μ'.withDensity f) := by
    refine Measure.withDensity.sigmaFinite_of_ne_top ?_ ?_
    · exact hf.withDensity_rnDeriv ν
    · refine (Measure.absolutelyContinuous_of_le ?_).ae_le hf_ne_top
      exact Measure.withDensity_rnDeriv_le _ _
  have h := Measure.rnDeriv_add' ((μ.singularPart ν).withDensity f) (μ'.withDensity f) ν
  refine (h.trans ?_).symm
  suffices ((μ.singularPart ν).withDensity f).rnDeriv ν =ᵐ[ν] 0 by
    filter_upwards [this] with x hx using by simp [hx]
  rw [Measure.rnDeriv_eq_zero]
  exact (Measure.mutuallySingular_singularPart μ ν).withDensity

lemma todo_right (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] {f : α → ℝ≥0∞}
    (hf : AEMeasurable f ν) (hf_ne_zero : ∀ᵐ x ∂ν, f x ≠ 0) (hf_ne_top : ∀ᵐ x ∂ν, f x ≠ ∞) :
    μ.rnDeriv (ν.withDensity f) =ᵐ[ν] (ν.withDensity (μ.rnDeriv ν)).rnDeriv (ν.withDensity f) := by
  conv_lhs => rw [μ.haveLebesgueDecomposition_add ν]
  have hν_ac : ν ≪ ν.withDensity f := withDensity_absolutelyContinuous' hf hf_ne_zero hf_ne_top
  have : SigmaFinite (ν.withDensity f) :=
    Measure.withDensity.sigmaFinite_of_ne_top hf hf_ne_top
  have h_add : (μ.singularPart ν + ν.withDensity (μ.rnDeriv ν)).rnDeriv (ν.withDensity f)
      =ᵐ[ν] (μ.singularPart ν).rnDeriv (ν.withDensity f) + _ :=
    hν_ac.ae_le (Measure.rnDeriv_add' (μ.singularPart ν) (ν.withDensity (μ.rnDeriv ν))
      (ν.withDensity f))
  refine h_add.trans ?_
  suffices (μ.singularPart ν).rnDeriv (ν.withDensity f) =ᵐ[ν] 0 by
    filter_upwards [this] with x hx
    rw [Pi.add_apply, hx, Pi.zero_apply, zero_add]
  refine hν_ac.ae_le ?_
  refine Measure.MutuallySingular.rnDeriv_ae_eq_zero ?_
  exact Measure.MutuallySingular.mono_ac (μ.mutuallySingular_singularPart ν)
    Measure.AbsolutelyContinuous.rfl (withDensity_absolutelyContinuous _ _)

lemma rnDeriv_withDensity_left_of_absolutelyContinuous  {ν : Measure α} [SigmaFinite μ]
  [SigmaFinite ν] (hμν : μ ≪ ν) {f : α → ℝ≥0∞} (hf : AEMeasurable f ν) :
    (μ.withDensity f).rnDeriv ν =ᵐ[ν] fun x ↦ f x * μ.rnDeriv ν x := by
  refine (Measure.eq_rnDeriv₀ ?_ Measure.MutuallySingular.zero_left ?_).symm
  · exact hf.mul (Measure.measurable_rnDeriv _ _).aemeasurable
  · ext1 s hs
    rw [zero_add, withDensity_apply _ hs, withDensity_apply _ hs]
    conv_lhs => rw [← Measure.withDensity_rnDeriv_eq _ _ hμν]
    rw [set_lintegral_withDensity_eq_set_lintegral_mul_non_measurable₀ _ _ _ hs]
    · congr with x
      rw [mul_comm]
      simp only [Pi.mul_apply]
    · refine ae_restrict_of_ae ?_
      exact Measure.rnDeriv_lt_top _ _
    · exact (Measure.measurable_rnDeriv _ _).aemeasurable

lemma rnDeriv_withDensity_left {μ ν : Measure α} [SigmaFinite μ] [SigmaFinite ν]
    {f : α → ℝ≥0∞} (hfμ : AEMeasurable f μ) (hfν : AEMeasurable f ν)
    (hf_ne_top : ∀ᵐ x ∂μ, f x ≠ ∞) :
    (μ.withDensity f).rnDeriv ν =ᵐ[ν] fun x ↦ f x * μ.rnDeriv ν x := by
  let μ' := ν.withDensity (μ.rnDeriv ν)
  have hμ'ν : μ' ≪ ν := withDensity_absolutelyContinuous _ _
  have h := rnDeriv_withDensity_left_of_absolutelyContinuous hμ'ν hfν
  have h1 : μ'.rnDeriv ν =ᵐ[ν] μ.rnDeriv ν :=
    Measure.rnDeriv_withDensity _ (Measure.measurable_rnDeriv _ _)
  have h2 : (μ'.withDensity f).rnDeriv ν =ᵐ[ν] (μ.withDensity f).rnDeriv ν := by
    exact todo_left μ ν hfμ hf_ne_top
  filter_upwards [h, h1, h2] with x hx hx1 hx2
  rw [← hx2, hx, hx1]

lemma rnDeriv_withDensity_right_of_absolutelyContinuous {ν : Measure α} [SigmaFinite μ]
    [SigmaFinite ν] (hμν : μ ≪ ν) {f : α → ℝ≥0∞} (hf : AEMeasurable f ν)
    (hf_ne_zero : ∀ᵐ x ∂ν, f x ≠ 0) (hf_ne_top : ∀ᵐ x ∂ν, f x ≠ ∞) :
    μ.rnDeriv (ν.withDensity f) =ᵐ[ν] fun x ↦ (f x)⁻¹ * μ.rnDeriv ν x := by
  have : SigmaFinite (ν.withDensity f) := Measure.withDensity.sigmaFinite_of_ne_top hf hf_ne_top
  refine (withDensity_absolutelyContinuous' hf hf_ne_zero hf_ne_top).ae_le ?_
  refine (Measure.eq_rnDeriv₀ (ν := ν.withDensity f) ?_ Measure.MutuallySingular.zero_left ?_).symm
  · refine AEMeasurable.mul ?_ (Measure.measurable_rnDeriv _ _).aemeasurable
    exact AEMeasurable.mono_ac hf.inv (withDensity_absolutelyContinuous _ _)
  · ext1 s hs
    conv_lhs => rw [← Measure.withDensity_rnDeriv_eq _ _ hμν]
    rw [zero_add, withDensity_apply _ hs, withDensity_apply _ hs]
    rw [set_lintegral_withDensity_eq_set_lintegral_mul_non_measurable₀ _ _ _ hs]
    · simp only [Pi.mul_apply]
      have : (fun a ↦ f a * ((f a)⁻¹ * μ.rnDeriv ν a)) =ᵐ[ν] μ.rnDeriv ν := by
        filter_upwards [hf_ne_zero, hf_ne_top] with x hx1 hx2
        simp [← mul_assoc, ENNReal.mul_inv_cancel, hx1, hx2]
      rw [lintegral_congr_ae (ae_restrict_of_ae this)]
    · refine ae_restrict_of_ae ?_
      filter_upwards [hf_ne_top] with x hx using hx.lt_top
    · exact hf.restrict

lemma rnDeriv_withDensity_right (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν]
    {f : α → ℝ≥0∞} (hf : AEMeasurable f ν) (hf_ne_zero : ∀ᵐ x ∂ν, f x ≠ 0)
    (hf_ne_top : ∀ᵐ x ∂ν, f x ≠ ∞) :
    μ.rnDeriv (ν.withDensity f) =ᵐ[ν] fun x ↦ (f x)⁻¹ * μ.rnDeriv ν x := by
  let μ' := ν.withDensity (μ.rnDeriv ν)
  have h₁ : μ.rnDeriv (ν.withDensity f) =ᵐ[ν] μ'.rnDeriv (ν.withDensity f) :=
    todo_right μ ν hf hf_ne_zero hf_ne_top
  have h₂ : μ.rnDeriv ν =ᵐ[ν] μ'.rnDeriv ν :=
    (Measure.rnDeriv_withDensity _ (Measure.measurable_rnDeriv _ _)).symm
  have : SigmaFinite μ' := Measure.withDensity.sigmaFinite_of_ne_top
    (Measure.measurable_rnDeriv _ _).aemeasurable (Measure.rnDeriv_ne_top _ _)
  have hμ' := rnDeriv_withDensity_right_of_absolutelyContinuous
    (withDensity_absolutelyContinuous ν (μ.rnDeriv ν)) hf hf_ne_zero hf_ne_top
  filter_upwards [h₁, h₂, hμ'] with x hx₁ hx₂ hx_eq
  rw [hx₁, hx₂, hx_eq]

end withDensity

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
  rw [logIntegralExp, exp_log]
  exact integral_exp_pos hf

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

lemma sigmaFinite_tilted [SigmaFinite μ] (hf : AEMeasurable f μ) :
    SigmaFinite (μ.tilted f) := by
  refine Measure.withDensity.sigmaFinite_ofReal ?_
  refine AEMeasurable.aestronglyMeasurable ?_
  exact measurable_exp.comp_aemeasurable (hf.sub aemeasurable_const)

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

lemma rnDeriv_tilted_left_self [SigmaFinite μ] (hf : AEMeasurable f μ) :
    (μ.tilted f).rnDeriv μ =ᵐ[μ] fun x ↦ ENNReal.ofReal (exp (f x - logIntegralExp μ f)) :=
  Measure.rnDeriv_withDensity₀ μ
    (measurable_exp.ennreal_ofReal.comp_aemeasurable (hf.sub aemeasurable_const))

lemma log_rnDeriv_tilted_left_self [SigmaFinite μ] (hf : AEMeasurable f μ) :
    (fun x ↦ log ((μ.tilted f).rnDeriv μ x).toReal) =ᵐ[μ] fun x ↦ f x - logIntegralExp μ f := by
  filter_upwards [rnDeriv_tilted_left_self hf] with x hx
  rw [hx, ENNReal.toReal_ofReal (exp_pos _).le, log_exp]

lemma rnDeriv_tilted_right (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν]
    (hf : AEMeasurable f ν) :
    μ.rnDeriv (ν.tilted f)
      =ᵐ[ν] fun x ↦ ENNReal.ofReal (exp (- f x + logIntegralExp ν f)) * μ.rnDeriv ν x := by
  refine (rnDeriv_withDensity_right μ ν ?_ ?_ ?_).trans ?_
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

lemma rnDeriv_tilted_left {μ ν : Measure α} [SigmaFinite μ] [SigmaFinite ν]
    (hfμ : AEMeasurable f μ) (hfν : AEMeasurable f ν) :
    (μ.tilted f).rnDeriv ν
      =ᵐ[ν] fun x ↦ ENNReal.ofReal (exp (f x - logIntegralExp μ f)) * μ.rnDeriv ν x := by
  let g := fun x ↦ ENNReal.ofReal (exp (f x - logIntegralExp μ f))
  refine rnDeriv_withDensity_left (μ := μ) (ν := ν) (f := g) ?_ ?_ ?_
  · exact measurable_exp.ennreal_ofReal.comp_aemeasurable (hfμ.sub aemeasurable_const)
  · exact measurable_exp.ennreal_ofReal.comp_aemeasurable (hfν.sub aemeasurable_const)
  · exact ae_of_all _ (fun x ↦ by simp)

lemma ofReal_rnDeriv_tilted_left {μ ν : Measure α} [SigmaFinite μ] [SigmaFinite ν]
    (hfμ : AEMeasurable f μ) (hfν : AEMeasurable f ν) :
    (fun x ↦ ((μ.tilted f).rnDeriv ν x).toReal)
      =ᵐ[ν] fun x ↦ exp (f x - logIntegralExp μ f) * (μ.rnDeriv ν x).toReal := by
  filter_upwards [rnDeriv_tilted_left hfμ hfν] with x hx
  rw [hx]
  simp only [ENNReal.toReal_mul, mul_eq_mul_right_iff, ENNReal.toReal_ofReal_eq_iff]
  exact Or.inl (exp_pos _).le

end tilted

end MeasureTheory
