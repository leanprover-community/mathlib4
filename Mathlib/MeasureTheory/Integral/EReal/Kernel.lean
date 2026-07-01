/-
Copyright (c) 2025 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré, Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Integral.EReal.EIntegral
public import Mathlib.Probability.Kernel.Composition.MeasureComp

/-!
# TODO

-/

@[expose] public section

open ProbabilityTheory

open scoped ENNReal

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α} {f g : α → EReal}

lemma eintegral_bind_of_nonneg {β : Type*} {mβ : MeasurableSpace β} {m : α → Measure β}
    {f : β → EReal} (hf_nonneg : ∀ x, 0 ≤ f x)
    (hμ : AEMeasurable m μ) (hf : AEMeasurable f (μ.bind m)) :
    ∫ᵉ x, f x ∂μ.bind m = ∫ᵉ a, ∫ᵉ x, f x ∂m a ∂μ := by
  rw [eintegral_of_nonneg hf_nonneg, μ.lintegral_bind hμ (by fun_prop), eintegral_of_nonneg]
  swap; · exact fun _ ↦ eintegral_nonneg hf_nonneg
  congr with x
  rw [eintegral_of_nonneg hf_nonneg]
  simp_rw [EReal.toENNReal_coe]

theorem eintegral_comp_measure {β : Type*} {mβ : MeasurableSpace β} {κ : Kernel α β} {f : β → EReal}
    (hf : Measurable f) (hf_int : EIntegrable f (κ ∘ₘ μ)) :
    ∫ᵉ x, f x ∂(κ ∘ₘ μ) = ∫ᵉ a, ∫ᵉ x, f x ∂κ a ∂μ := by
  rw [eintegral_eq_posPartFun_sub_negPartFun f, eintegral_bind_of_nonneg (by simp) κ.aemeasurable,
    eintegral_bind_of_nonneg (by simp) κ.aemeasurable]
  rotate_left
  · fun_prop
  · fun_prop
  rw [← eintegral_sub_of_nonneg]
  rotate_left
  · exact fun _ ↦ eintegral_nonneg (by simp)
  · exact fun _ ↦ eintegral_nonneg (by simp)
  · simp_rw [eintegral_of_nonneg (posPartFun_nonneg f)]
    suffices AEMeasurable (fun a ↦ ∫⁻ x, (f⁺ x).toENNReal ∂κ a) μ by fun_prop
    exact (Measurable.lintegral_kernel (by fun_prop)).aemeasurable
  · simp_rw [eintegral_of_nonneg (negPartFun_nonneg f)]
    suffices AEMeasurable (fun a ↦ ∫⁻ x, (f⁻ x).toENNReal ∂κ a) μ by fun_prop
    exact (Measurable.lintegral_kernel (by fun_prop)).aemeasurable
  · refine ne_of_lt ?_
    cases hf_int.eintegral_posPartFun_ne_top_or_eintegral_negPartFun_ne_top with
    | inl h =>
      calc ∫ᵉ x, min (∫ᵉ y, f⁺ y ∂κ x) (∫ᵉ y, f⁻ y ∂κ x) ∂μ
      _ ≤ ∫ᵉ x, ∫ᵉ y, f⁺ y ∂κ x ∂μ := eintegral_mono (fun _ ↦ min_le_left _ _)
      _ = ∫ᵉ p, f⁺ p ∂(κ ∘ₘ μ) := by
        rw [eintegral_bind_of_nonneg (posPartFun_nonneg f) κ.aemeasurable (by fun_prop)]
      _ < ⊤ := h.lt_top
    | inr h =>
      calc ∫ᵉ x, min (∫ᵉ y, f⁺ y ∂κ x) (∫ᵉ y, f⁻ y ∂κ x) ∂μ
      _ ≤ ∫ᵉ x, ∫ᵉ y, f⁻ y ∂κ x ∂μ := eintegral_mono (fun _ ↦ min_le_right _ _)
      _ = ∫ᵉ p, f⁻ p ∂(κ ∘ₘ μ) := by
        rw [eintegral_bind_of_nonneg (negPartFun_nonneg f) κ.aemeasurable (by fun_prop)]
      _ < ⊤ := h.lt_top
  congr with x
  rw [← eintegral_sub_of_nonneg_of_eq_zero (by simp) (by simp)
    (posPartFun_eq_zero_or_negPartFun_eq_zero f)]
  simp_rw [posPartFun_sub_negPartFun f]

lemma eintegral_comp_measure_le {β : Type*} {mβ : MeasurableSpace β} {κ : Kernel α β}
    {f : β → EReal} (hf : Measurable f) :
    ∫ᵉ x, f x ∂(κ ∘ₘ μ) ≤ ∫ᵉ a, ∫ᵉ x, f x ∂κ a ∂μ := by
  by_cases hf_int : EIntegrable f (κ ∘ₘ μ)
  · rw [eintegral_comp_measure hf hf_int]
  · simp [eintegral_of_not_eintegrable hf_int]

end MeasureTheory
