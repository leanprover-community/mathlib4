/-
Copyright (c) 2025 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré, Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Integral.EReal.EIntegral
public import Mathlib.Probability.Kernel.Composition.MeasureComp

/-!
# Extended integral with respect to a composition of a kernel and a measure

## Main statements

* `eintegral_bind`: for `f : β → EReal` which is `EIntegrable` with respect to `μ.bind m`,
  `∫ᵉ x, f x ∂μ.bind m = ∫ᵉ a, ∫ᵉ x, f x ∂m a ∂μ`.
* `eintegral_comp_measure`: for `f : β → EReal` which is `EIntegrable` with respect to `κ ∘ₘ μ`,
  `∫ᵉ x, f x ∂(κ ∘ₘ μ) = ∫ᵉ a, ∫ᵉ x, f x ∂κ a ∂μ`.
* `eintegral_comp_measure_le`: the inequality `∫ᵉ x, f x ∂(κ ∘ₘ μ) ≤ ∫ᵉ a, ∫ᵉ x, f x ∂κ a ∂μ`
  holds without integrability assumption.

-/

@[expose] public section

open ProbabilityTheory

open scoped ENNReal

namespace MeasureTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ : Measure α}
  {f : β → EReal}

lemma eintegral_bind {m : α → Measure β} (hm : AEMeasurable m μ) (hf : AEMeasurable f (μ.bind m))
    (hf_int : EIntegrable f (μ.bind m)) :
    ∫ᵉ x, f x ∂μ.bind m = ∫ᵉ a, ∫ᵉ x, f x ∂m a ∂μ := by
  have h_pos : AEMeasurable (fun x ↦ (f x).toENNReal) (μ.bind m) := by fun_prop
  have h_neg : AEMeasurable (fun x ↦ (-f x).toENNReal) (μ.bind m) := by fun_prop
  have h_eq a : ∫ᵉ x, f x ∂m a = ∫⁻ x, (f x).toENNReal ∂m a - ∫⁻ x, (-f x).toENNReal ∂m a := rfl
  simp_rw [h_eq]
  rw [eintegral_coe_ennreal_sub (u := fun a ↦ ∫⁻ x, (f x).toENNReal ∂m a)
      (v := fun a ↦ ∫⁻ x, (-f x).toENNReal ∂m a)
      ((Measure.aemeasurable_lintegral h_pos).comp_aemeasurable hm)
      ((Measure.aemeasurable_lintegral h_neg).comp_aemeasurable hm),
    ← Measure.lintegral_bind hm h_pos, ← Measure.lintegral_bind hm h_neg]
  · rfl
  · rwa [← Measure.lintegral_bind hm h_pos, ← Measure.lintegral_bind hm h_neg]

theorem eintegral_comp_measure {κ : Kernel α β} (hf : AEMeasurable f (κ ∘ₘ μ))
    (hf_int : EIntegrable f (κ ∘ₘ μ)) :
    ∫ᵉ x, f x ∂(κ ∘ₘ μ) = ∫ᵉ a, ∫ᵉ x, f x ∂κ a ∂μ :=
  eintegral_bind κ.aemeasurable hf hf_int

lemma eintegral_comp_measure_le {κ : Kernel α β} (hf : AEMeasurable f (κ ∘ₘ μ)) :
    ∫ᵉ x, f x ∂(κ ∘ₘ μ) ≤ ∫ᵉ a, ∫ᵉ x, f x ∂κ a ∂μ := by
  by_cases hf_int : EIntegrable f (κ ∘ₘ μ)
  · rw [eintegral_comp_measure hf hf_int]
  · simp [eintegral_of_not_eintegrable hf_int]

end MeasureTheory
