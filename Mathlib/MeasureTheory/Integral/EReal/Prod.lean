/-
Copyright (c) 2025 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré, Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Integral.EReal.EIntegral
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Extended integral with respect to a product measure

## Main statements

* `eintegral_prod`: **Fubini's theorem** for `EIntegrable` extended real-valued functions:
  `∫ᵉ z, f z ∂(μ.prod ν) = ∫ᵉ x, ∫ᵉ y, f (x, y) ∂ν ∂μ`.
* `eintegral_prod_symm`: the same with the order of integration swapped.

-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {μ : Measure α} {ν : Measure β} [SFinite ν]

/-- **Fubini's theorem** for `EIntegrable` extended real-valued functions: the integral with respect
to the product measure equals the iterated integral. -/
lemma eintegral_prod
    (f : α × β → EReal) (hf : AEMeasurable f (μ.prod ν)) (hf_int : EIntegrable f (μ.prod ν)) :
    ∫ᵉ z, f z ∂(μ.prod ν) = ∫ᵉ x, ∫ᵉ y, f (x, y) ∂ν ∂μ := by
  have h_eq x : ∫ᵉ y, f (x, y) ∂ν
      = ∫⁻ y, (f (x, y)).toENNReal ∂ν - ∫⁻ y, (-f (x, y)).toENNReal ∂ν := rfl
  have h_pos := lintegral_prod (μ := μ) (ν := ν) (fun z ↦ (f z).toENNReal) (by fun_prop)
  have h_neg := lintegral_prod (μ := μ) (ν := ν) (fun z ↦ (-f z).toENNReal) (by fun_prop)
  simp_rw [h_eq]
  rw [eintegral_coe_ennreal_sub
      (AEMeasurable.lintegral_prod_right' (f := fun z ↦ (f z).toENNReal) (by fun_prop))
      (AEMeasurable.lintegral_prod_right' (f := fun z ↦ (-f z).toENNReal) (by fun_prop)),
    ← h_pos, ← h_neg]
  · rfl
  · rwa [← h_pos, ← h_neg]

variable [SFinite μ]

lemma eintegral_prod_swap (f : α × β → EReal) :
    ∫ᵉ z, f z.swap ∂(ν.prod μ) = ∫ᵉ z, f z ∂(μ.prod ν) := by
  simp only [eintegral]
  rw [lintegral_prod_swap (fun z ↦ (f z).toENNReal), lintegral_prod_swap (fun z ↦ (-f z).toENNReal)]

lemma EIntegrable.swap {f : α × β → EReal} (hf : EIntegrable f (μ.prod ν)) :
    EIntegrable (fun z ↦ f z.swap) (ν.prod μ) := by
  simpa [EIntegrable, lintegral_prod_swap (fun z ↦ (f z).toENNReal),
    lintegral_prod_swap (fun z ↦ (-f z).toENNReal)] using hf

/-- **Fubini's theorem** for `EIntegrable` extended real-valued functions, with the order of
integration swapped. -/
lemma eintegral_prod_symm
    (f : α × β → EReal) (hf : AEMeasurable f (μ.prod ν)) (hf_int : EIntegrable f (μ.prod ν)) :
    ∫ᵉ z, f z ∂(μ.prod ν) = ∫ᵉ y, ∫ᵉ x, f (x, y) ∂μ ∂ν := by
  rw [← eintegral_prod_swap f]
  exact eintegral_prod _ hf.prod_swap hf_int.swap

end MeasureTheory
