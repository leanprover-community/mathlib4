/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Kernel.Disintegration.Basic

/-!
# Integral

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

open MeasureTheory ProbabilityTheory

open scoped ENNReal

namespace ProbabilityTheory

variable {α β Ω : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]

section Lintegral

variable [CountableOrStandardBorel α β] {κ : kernel α (β × Ω)} [IsFiniteKernel κ]
  {f : β × Ω → ℝ≥0∞}

lemma lintegral_condKernel_mem (a : α) {s : Set (β × Ω)} (hs : MeasurableSet s) :
    ∫⁻ x, kernel.condKernel κ (a, x) {y | (x, y) ∈ s} ∂(kernel.fst κ a) = κ a s := by
  conv_rhs => rw [← kernel.compProd_fst_condKernel κ]
  simp_rw [kernel.compProd_apply _ _ _ hs]

lemma set_lintegral_condKernel_eq_measure_prod (a : α) {s : Set β} (hs : MeasurableSet s) {t : Set Ω}
    (ht : MeasurableSet t) :
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

variable [CountableOrStandardBorel α β] {κ : kernel α (β × Ω)} [IsFiniteKernel κ]
  {E : Type*} {f : β × Ω → E} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

lemma integral_condKernel (a : α) (hf : Integrable f (κ a)) :
    ∫ b, ∫ ω, f (b, ω) ∂(kernel.condKernel κ (a, b)) ∂(kernel.fst κ a) = ∫ x, f x ∂(κ a) := by
  conv_rhs => rw [← kernel.compProd_fst_condKernel κ]
  rw [← kernel.compProd_fst_condKernel κ] at hf
  rw [integral_compProd hf]

lemma set_integral_condKernel (a : α) {s : Set β} (hs : MeasurableSet s)
    {t : Set Ω} (ht : MeasurableSet t) (hf : IntegrableOn f (s ×ˢ t) (κ a)) :
    ∫ b in s, ∫ ω in t, f (b, ω) ∂(kernel.condKernel κ (a, b)) ∂(kernel.fst κ a)
      = ∫ x in s ×ˢ t, f x ∂(κ a) := by
  conv_rhs => rw [← kernel.compProd_fst_condKernel κ]
  rw [← kernel.compProd_fst_condKernel κ] at hf
  rw [set_integral_compProd hs ht hf]

lemma set_integral_condKernel_univ_right (a : α) {s : Set β} (hs : MeasurableSet s)
    (hf : IntegrableOn f (s ×ˢ Set.univ) (κ a)) :
    ∫ b in s, ∫ ω, f (b, ω) ∂(kernel.condKernel κ (a, b)) ∂(kernel.fst κ a)
      = ∫ x in s ×ˢ Set.univ, f x ∂(κ a) := by
  rw [← set_integral_condKernel a hs MeasurableSet.univ hf]; simp_rw [Measure.restrict_univ]

lemma set_integral_condKernel_univ_left (a : α) {t : Set Ω} (ht : MeasurableSet t)
    (hf : IntegrableOn f (Set.univ ×ˢ t) (κ a)) :
    ∫ b, ∫ ω in t, f (b, ω) ∂(kernel.condKernel κ (a, b)) ∂(kernel.fst κ a)
      = ∫ x in Set.univ ×ˢ t, f x ∂(κ a) := by
  rw [← set_integral_condKernel a MeasurableSet.univ ht hf]; simp_rw [Measure.restrict_univ]

end Integral

end ProbabilityTheory

namespace MeasureTheory.Measure

variable {α β Ω : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]

section Lintegral

variable [CountableOrStandardBorel α β] {ρ : Measure (β × Ω)} [IsFiniteMeasure ρ]
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
  {E : Type*} {f : β × Ω → E} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

lemma integral_condKernel (hf : Integrable f ρ) :
    ∫ b, ∫ ω, f (b, ω) ∂(ρ.condKernel b) ∂ρ.fst = ∫ x, f x ∂ρ := by
  conv_rhs => rw [← compProd_fst_condKernel ρ]
  rw [← compProd_fst_condKernel ρ] at hf
  rw [integral_compProd hf]
#align probability_theory.integral_cond_kernel MeasureTheory.Measure.integral_condKernel

lemma set_integral_condKernel {s : Set β} (hs : MeasurableSet s)
    {t : Set Ω} (ht : MeasurableSet t) (hf : IntegrableOn f (s ×ˢ t) ρ) :
    ∫ b in s, ∫ ω in t, f (b, ω) ∂(ρ.condKernel b) ∂ρ.fst = ∫ x in s ×ˢ t, f x ∂ρ := by
  conv_rhs => rw [← compProd_fst_condKernel ρ]
  rw [← compProd_fst_condKernel ρ] at hf
  rw [set_integral_compProd hs ht hf]
#align probability_theory.set_integral_cond_kernel MeasureTheory.Measure.set_integral_condKernel

lemma set_integral_condKernel_univ_right {s : Set β} (hs : MeasurableSet s)
    (hf : IntegrableOn f (s ×ˢ Set.univ) ρ) :
    ∫ b in s, ∫ ω, f (b, ω) ∂(ρ.condKernel b) ∂ρ.fst = ∫ x in s ×ˢ Set.univ, f x ∂ρ := by
  rw [← set_integral_condKernel hs MeasurableSet.univ hf]; simp_rw [Measure.restrict_univ]
#align probability_theory.set_integral_cond_kernel_univ_right MeasureTheory.Measure.set_integral_condKernel_univ_right

lemma set_integral_condKernel_univ_left {t : Set Ω} (ht : MeasurableSet t)
    (hf : IntegrableOn f (Set.univ ×ˢ t) ρ) :
    ∫ b, ∫ ω in t, f (b, ω) ∂(ρ.condKernel b) ∂ρ.fst = ∫ x in Set.univ ×ˢ t, f x ∂ρ := by
  rw [← set_integral_condKernel MeasurableSet.univ ht hf]; simp_rw [Measure.restrict_univ]
#align probability_theory.set_integral_cond_kernel_univ_left MeasureTheory.Measure.set_integral_condKernel_univ_left

end Integral

end MeasureTheory.Measure
