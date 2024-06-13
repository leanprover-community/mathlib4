/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Kernel.Disintegration.Basic

/-!
# Lebesgue and Bochner integrals of conditional kernels

Integrals of `ProbabilityTheory.kernel.condKernel` and `MeasureTheory.Measure.condKernel`.

## Main statements

* `ProbabilityTheory.setIntegral_condKernel`: the integral
  `∫ b in s, ∫ ω in t, f (b, ω) ∂(kernel.condKernel κ (a, b)) ∂(kernel.fst κ a)` is equal to
  `∫ x in s ×ˢ t, f x ∂(κ a)`.
* `MeasureTheory.Measure.setIntegral_condKernel`:
  `∫ b in s, ∫ ω in t, f (b, ω) ∂(ρ.condKernel b) ∂ρ.fst = ∫ x in s ×ˢ t, f x ∂ρ`

Corresponding statements for the Lebesgue integral and/or without the sets `s` and `t` are also
provided.
-/

open MeasureTheory ProbabilityTheory MeasurableSpace

open scoped ENNReal

namespace ProbabilityTheory

variable {α β Ω : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]

section Lintegral

variable [CountableOrCountablyGenerated α β] {κ : kernel α (β × Ω)} [IsFiniteKernel κ]
  {f : β × Ω → ℝ≥0∞}

lemma lintegral_condKernel_mem (a : α) {s : Set (β × Ω)} (hs : MeasurableSet s) :
    ∫⁻ x, kernel.condKernel κ (a, x) {y | (x, y) ∈ s} ∂(kernel.fst κ a) = κ a s := by
  conv_rhs => rw [← kernel.compProd_fst_condKernel κ]
  simp_rw [kernel.compProd_apply _ _ _ hs]

lemma set_lintegral_condKernel_eq_measure_prod (a : α) {s : Set β} (hs : MeasurableSet s)
    {t : Set Ω} (ht : MeasurableSet t) :
    ∫⁻ b in s, kernel.condKernel κ (a, b) t ∂(kernel.fst κ a) = κ a (s ×ˢ t) := by
  have : κ a (s ×ˢ t) = (kernel.fst κ ⊗ₖ kernel.condKernel κ) a (s ×ˢ t) := by
    congr; exact (kernel.compProd_fst_condKernel κ).symm
  rw [this, kernel.compProd_apply _ _ _ (hs.prod ht)]
  classical
  have : ∀ b, kernel.condKernel κ (a, b) {c | (b, c) ∈ s ×ˢ t}
      = s.indicator (fun b ↦ kernel.condKernel κ (a, b) t) b := by
    intro b
    by_cases hb : b ∈ s <;> simp [hb]
  simp_rw [this]
  rw [lintegral_indicator _ hs]

lemma lintegral_condKernel (hf : Measurable f) (a : α) :
    ∫⁻ b, ∫⁻ ω, f (b, ω) ∂(kernel.condKernel κ (a, b)) ∂(kernel.fst κ a) = ∫⁻ x, f x ∂(κ a) := by
  conv_rhs => rw [← kernel.compProd_fst_condKernel κ]
  rw [kernel.lintegral_compProd _ _ _ hf]

lemma set_lintegral_condKernel (hf : Measurable f) (a : α) {s : Set β}
    (hs : MeasurableSet s) {t : Set Ω} (ht : MeasurableSet t) :
    ∫⁻ b in s, ∫⁻ ω in t, f (b, ω) ∂(kernel.condKernel κ (a, b)) ∂(kernel.fst κ a)
      = ∫⁻ x in s ×ˢ t, f x ∂(κ a) := by
  conv_rhs => rw [← kernel.compProd_fst_condKernel κ]
  rw [kernel.set_lintegral_compProd _ _ _ hf hs ht]

lemma set_lintegral_condKernel_univ_right (hf : Measurable f) (a : α) {s : Set β}
    (hs : MeasurableSet s) :
    ∫⁻ b in s, ∫⁻ ω, f (b, ω) ∂(kernel.condKernel κ (a, b)) ∂(kernel.fst κ a)
      = ∫⁻ x in s ×ˢ Set.univ, f x ∂(κ a) := by
  rw [← set_lintegral_condKernel hf a hs MeasurableSet.univ]; simp_rw [Measure.restrict_univ]

lemma set_lintegral_condKernel_univ_left (hf : Measurable f) (a : α) {t : Set Ω}
    (ht : MeasurableSet t) :
    ∫⁻ b, ∫⁻ ω in t, f (b, ω) ∂(kernel.condKernel κ (a, b)) ∂(kernel.fst κ a)
      = ∫⁻ x in Set.univ ×ˢ t, f x ∂(κ a) := by
  rw [← set_lintegral_condKernel hf a MeasurableSet.univ ht]; simp_rw [Measure.restrict_univ]

end Lintegral

section Integral

variable [CountableOrCountablyGenerated α β] {κ : kernel α (β × Ω)} [IsFiniteKernel κ]
  {E : Type*} {f : β × Ω → E} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma _root_.MeasureTheory.AEStronglyMeasurable.integral_kernel_condKernel (a : α)
    (hf : AEStronglyMeasurable f (κ a)) :
    AEStronglyMeasurable (fun x ↦ ∫ y, f (x, y) ∂(kernel.condKernel κ (a, x)))
      (kernel.fst κ a) := by
  rw [← kernel.compProd_fst_condKernel κ] at hf
  exact AEStronglyMeasurable.integral_kernel_compProd hf

lemma integral_condKernel (a : α) (hf : Integrable f (κ a)) :
    ∫ b, ∫ ω, f (b, ω) ∂(kernel.condKernel κ (a, b)) ∂(kernel.fst κ a) = ∫ x, f x ∂(κ a) := by
  conv_rhs => rw [← kernel.compProd_fst_condKernel κ]
  rw [← kernel.compProd_fst_condKernel κ] at hf
  rw [integral_compProd hf]

lemma setIntegral_condKernel (a : α) {s : Set β} (hs : MeasurableSet s)
    {t : Set Ω} (ht : MeasurableSet t) (hf : IntegrableOn f (s ×ˢ t) (κ a)) :
    ∫ b in s, ∫ ω in t, f (b, ω) ∂(kernel.condKernel κ (a, b)) ∂(kernel.fst κ a)
      = ∫ x in s ×ˢ t, f x ∂(κ a) := by
  conv_rhs => rw [← kernel.compProd_fst_condKernel κ]
  rw [← kernel.compProd_fst_condKernel κ] at hf
  rw [setIntegral_compProd hs ht hf]

@[deprecated (since := "2024-04-17")]
alias set_integral_condKernel := setIntegral_condKernel

lemma setIntegral_condKernel_univ_right (a : α) {s : Set β} (hs : MeasurableSet s)
    (hf : IntegrableOn f (s ×ˢ Set.univ) (κ a)) :
    ∫ b in s, ∫ ω, f (b, ω) ∂(kernel.condKernel κ (a, b)) ∂(kernel.fst κ a)
      = ∫ x in s ×ˢ Set.univ, f x ∂(κ a) := by
  rw [← setIntegral_condKernel a hs MeasurableSet.univ hf]; simp_rw [Measure.restrict_univ]

@[deprecated (since := "2024-04-17")]
alias set_integral_condKernel_univ_right := setIntegral_condKernel_univ_right

lemma setIntegral_condKernel_univ_left (a : α) {t : Set Ω} (ht : MeasurableSet t)
    (hf : IntegrableOn f (Set.univ ×ˢ t) (κ a)) :
    ∫ b, ∫ ω in t, f (b, ω) ∂(kernel.condKernel κ (a, b)) ∂(kernel.fst κ a)
      = ∫ x in Set.univ ×ˢ t, f x ∂(κ a) := by
  rw [← setIntegral_condKernel a MeasurableSet.univ ht hf]; simp_rw [Measure.restrict_univ]

@[deprecated (since := "2024-04-17")]
alias set_integral_condKernel_univ_left := setIntegral_condKernel_univ_left

end Integral

end ProbabilityTheory

namespace MeasureTheory.Measure

variable {α β Ω : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]

section Lintegral

variable [CountableOrCountablyGenerated α β] {ρ : Measure (β × Ω)} [IsFiniteMeasure ρ]
  {f : β × Ω → ℝ≥0∞}

lemma lintegral_condKernel_mem {s : Set (β × Ω)} (hs : MeasurableSet s) :
    ∫⁻ x, ρ.condKernel x {y | (x, y) ∈ s} ∂ρ.fst = ρ s := by
  conv_rhs => rw [← compProd_fst_condKernel ρ]
  simp_rw [compProd_apply hs]
  rfl
#align probability_theory.lintegral_cond_kernel_mem MeasureTheory.Measure.lintegral_condKernel_mem

lemma set_lintegral_condKernel_eq_measure_prod {s : Set β} (hs : MeasurableSet s) {t : Set Ω}
    (ht : MeasurableSet t) :
    ∫⁻ b in s, ρ.condKernel b t ∂ρ.fst = ρ (s ×ˢ t) := by
  have : ρ (s ×ˢ t) = (ρ.fst ⊗ₘ ρ.condKernel) (s ×ˢ t) := by
    congr; exact (compProd_fst_condKernel ρ).symm
  rw [this, compProd_apply (hs.prod ht)]
  classical
  have : ∀ b, ρ.condKernel b (Prod.mk b ⁻¹' s ×ˢ t)
      = s.indicator (fun b ↦ ρ.condKernel b t) b := by
    intro b
    by_cases hb : b ∈ s <;> simp [hb]
  simp_rw [this]
  rw [lintegral_indicator _ hs]
#align probability_theory.set_lintegral_cond_kernel_eq_measure_prod MeasureTheory.Measure.set_lintegral_condKernel_eq_measure_prod

lemma lintegral_condKernel (hf : Measurable f) :
    ∫⁻ b, ∫⁻ ω, f (b, ω) ∂(ρ.condKernel b) ∂ρ.fst = ∫⁻ x, f x ∂ρ := by
  conv_rhs => rw [← compProd_fst_condKernel ρ]
  rw [lintegral_compProd hf]
#align probability_theory.lintegral_cond_kernel MeasureTheory.Measure.lintegral_condKernel

lemma set_lintegral_condKernel (hf : Measurable f) {s : Set β}
    (hs : MeasurableSet s) {t : Set Ω} (ht : MeasurableSet t) :
    ∫⁻ b in s, ∫⁻ ω in t, f (b, ω) ∂(ρ.condKernel b) ∂ρ.fst
      = ∫⁻ x in s ×ˢ t, f x ∂ρ := by
  conv_rhs => rw [← compProd_fst_condKernel ρ]
  rw [set_lintegral_compProd  hf hs ht]
#align probability_theory.set_lintegral_cond_kernel MeasureTheory.Measure.set_lintegral_condKernel

lemma set_lintegral_condKernel_univ_right (hf : Measurable f) {s : Set β}
    (hs : MeasurableSet s) :
    ∫⁻ b in s, ∫⁻ ω, f (b, ω) ∂(ρ.condKernel b) ∂ρ.fst
      = ∫⁻ x in s ×ˢ Set.univ, f x ∂ρ := by
  rw [← set_lintegral_condKernel hf hs MeasurableSet.univ]; simp_rw [Measure.restrict_univ]
#align probability_theory.set_lintegral_cond_kernel_univ_right MeasureTheory.Measure.set_lintegral_condKernel_univ_right

lemma set_lintegral_condKernel_univ_left (hf : Measurable f) {t : Set Ω}
    (ht : MeasurableSet t) :
    ∫⁻ b, ∫⁻ ω in t, f (b, ω) ∂(ρ.condKernel b) ∂ρ.fst
      = ∫⁻ x in Set.univ ×ˢ t, f x ∂ρ := by
  rw [← set_lintegral_condKernel hf MeasurableSet.univ ht]; simp_rw [Measure.restrict_univ]
#align probability_theory.set_lintegral_cond_kernel_univ_left MeasureTheory.Measure.set_lintegral_condKernel_univ_left

end Lintegral

section Integral

variable {ρ : Measure (β × Ω)} [IsFiniteMeasure ρ]
  {E : Type*} {f : β × Ω → E} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma _root_.MeasureTheory.AEStronglyMeasurable.integral_condKernel
    (hf : AEStronglyMeasurable f ρ) :
    AEStronglyMeasurable (fun x ↦ ∫ y, f (x, y) ∂ρ.condKernel x) ρ.fst := by
  rw [← ρ.compProd_fst_condKernel] at hf
  exact AEStronglyMeasurable.integral_kernel_compProd hf
#align measure_theory.ae_strongly_measurable.integral_cond_kernel MeasureTheory.AEStronglyMeasurable.integral_condKernel

lemma integral_condKernel (hf : Integrable f ρ) :
    ∫ b, ∫ ω, f (b, ω) ∂(ρ.condKernel b) ∂ρ.fst = ∫ x, f x ∂ρ := by
  conv_rhs => rw [← compProd_fst_condKernel ρ]
  rw [← compProd_fst_condKernel ρ] at hf
  rw [integral_compProd hf]
#align probability_theory.integral_cond_kernel MeasureTheory.Measure.integral_condKernel

lemma setIntegral_condKernel {s : Set β} (hs : MeasurableSet s)
    {t : Set Ω} (ht : MeasurableSet t) (hf : IntegrableOn f (s ×ˢ t) ρ) :
    ∫ b in s, ∫ ω in t, f (b, ω) ∂(ρ.condKernel b) ∂ρ.fst = ∫ x in s ×ˢ t, f x ∂ρ := by
  conv_rhs => rw [← compProd_fst_condKernel ρ]
  rw [← compProd_fst_condKernel ρ] at hf
  rw [setIntegral_compProd hs ht hf]
#align probability_theory.set_integral_cond_kernel MeasureTheory.Measure.setIntegral_condKernel

@[deprecated (since := "2024-04-17")]
alias set_integral_condKernel := setIntegral_condKernel

lemma setIntegral_condKernel_univ_right {s : Set β} (hs : MeasurableSet s)
    (hf : IntegrableOn f (s ×ˢ Set.univ) ρ) :
    ∫ b in s, ∫ ω, f (b, ω) ∂(ρ.condKernel b) ∂ρ.fst = ∫ x in s ×ˢ Set.univ, f x ∂ρ := by
  rw [← setIntegral_condKernel hs MeasurableSet.univ hf]; simp_rw [Measure.restrict_univ]
#align probability_theory.set_integral_cond_kernel_univ_right MeasureTheory.Measure.setIntegral_condKernel_univ_right

@[deprecated (since := "2024-04-17")]
alias set_integral_condKernel_univ_right := setIntegral_condKernel_univ_right

lemma setIntegral_condKernel_univ_left {t : Set Ω} (ht : MeasurableSet t)
    (hf : IntegrableOn f (Set.univ ×ˢ t) ρ) :
    ∫ b, ∫ ω in t, f (b, ω) ∂(ρ.condKernel b) ∂ρ.fst = ∫ x in Set.univ ×ˢ t, f x ∂ρ := by
  rw [← setIntegral_condKernel MeasurableSet.univ ht hf]; simp_rw [Measure.restrict_univ]
#align probability_theory.set_integral_cond_kernel_univ_left MeasureTheory.Measure.setIntegral_condKernel_univ_left

@[deprecated (since := "2024-04-17")]
alias set_integral_condKernel_univ_left := setIntegral_condKernel_univ_left

end Integral

end MeasureTheory.Measure

namespace MeasureTheory

/-! ### Integrability

We place these lemmas in the `MeasureTheory` namespace to enable dot notation. -/

open ProbabilityTheory

variable {α Ω E F : Type*} {mα : MeasurableSpace α} [MeasurableSpace Ω]
  [StandardBorelSpace Ω] [Nonempty Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] {ρ : Measure (α × Ω)} [IsFiniteMeasure ρ]

theorem AEStronglyMeasurable.ae_integrable_condKernel_iff {f : α × Ω → F}
    (hf : AEStronglyMeasurable f ρ) :
    (∀ᵐ a ∂ρ.fst, Integrable (fun ω ↦ f (a, ω)) (ρ.condKernel a)) ∧
      Integrable (fun a ↦ ∫ ω, ‖f (a, ω)‖ ∂ρ.condKernel a) ρ.fst ↔ Integrable f ρ := by
  rw [← ρ.compProd_fst_condKernel] at hf
  conv_rhs => rw [← ρ.compProd_fst_condKernel]
  rw [Measure.integrable_compProd_iff hf]
#align measure_theory.ae_strongly_measurable.ae_integrable_cond_kernel_iff MeasureTheory.AEStronglyMeasurable.ae_integrable_condKernel_iff

theorem Integrable.condKernel_ae {f : α × Ω → F} (hf_int : Integrable f ρ) :
    ∀ᵐ a ∂ρ.fst, Integrable (fun ω ↦ f (a, ω)) (ρ.condKernel a) := by
  have hf_ae : AEStronglyMeasurable f ρ := hf_int.1
  rw [← hf_ae.ae_integrable_condKernel_iff] at hf_int
  exact hf_int.1
#align measure_theory.integrable.cond_kernel_ae MeasureTheory.Integrable.condKernel_ae

theorem Integrable.integral_norm_condKernel {f : α × Ω → F} (hf_int : Integrable f ρ) :
    Integrable (fun x ↦ ∫ y, ‖f (x, y)‖ ∂ρ.condKernel x) ρ.fst := by
  have hf_ae : AEStronglyMeasurable f ρ := hf_int.1
  rw [← hf_ae.ae_integrable_condKernel_iff] at hf_int
  exact hf_int.2
#align measure_theory.integrable.integral_norm_cond_kernel MeasureTheory.Integrable.integral_norm_condKernel

theorem Integrable.norm_integral_condKernel {f : α × Ω → E} (hf_int : Integrable f ρ) :
    Integrable (fun x ↦ ‖∫ y, f (x, y) ∂ρ.condKernel x‖) ρ.fst := by
  refine hf_int.integral_norm_condKernel.mono hf_int.1.integral_condKernel.norm ?_
  refine Filter.eventually_of_forall fun x ↦ ?_
  rw [norm_norm]
  refine (norm_integral_le_integral_norm _).trans_eq (Real.norm_of_nonneg ?_).symm
  exact integral_nonneg_of_ae (Filter.eventually_of_forall fun y ↦ norm_nonneg _)
#align measure_theory.integrable.norm_integral_cond_kernel MeasureTheory.Integrable.norm_integral_condKernel

theorem Integrable.integral_condKernel {f : α × Ω → E} (hf_int : Integrable f ρ) :
    Integrable (fun x ↦ ∫ y, f (x, y) ∂ρ.condKernel x) ρ.fst :=
  (integrable_norm_iff hf_int.1.integral_condKernel).mp hf_int.norm_integral_condKernel
#align measure_theory.integrable.integral_cond_kernel MeasureTheory.Integrable.integral_condKernel

end MeasureTheory
