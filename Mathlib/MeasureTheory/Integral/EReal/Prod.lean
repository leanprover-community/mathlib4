/-
Copyright (c) 2025 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré, Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Integral.EReal.EIntegral
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# TODO

## Main statements

* `eintegral_prod`: Fubini's theorem for extended real-valued functions on product measures,
  allowing interchange of integration order.

-/

@[expose] public section

open ProbabilityTheory

open scoped ENNReal



namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α} {f g : α → EReal}

/-- Fubini's theorem for extended reals: the integral over the product equals the iterated
integral. -/
lemma eintegral_prod {β : Type*} {mβ : MeasurableSpace β} {ν : Measure β} [SFinite ν]
    (f : α × β → EReal) (hf : AEMeasurable f (μ.prod ν)) (hf_int : EIntegrable f (μ.prod ν)) :
    ∫ᵉ z, f z ∂(μ.prod ν) = ∫ᵉ x, ∫ᵉ y, f (x, y) ∂ν ∂μ := by
  set u : α × β → ℝ≥0∞ := fun z => (f z).toENNReal
  set v : α × β → ℝ≥0∞ := fun z => (-f z).toENNReal
  have hf_eq : f = fun z => (u z : EReal) - (v z : EReal) := by
    simp only [u, v]
    ext z
    rcases le_total (f z) 0 with h | h <;> simp [h]
  rw [hf_eq]
  have hu_aemeasurable : AEMeasurable u (μ.prod ν) := by fun_prop
  have hv_aemeasurable : AEMeasurable v (μ.prod ν) := by fun_prop
  have h_u_v : (∫⁻ x, u x ∂(μ.prod ν) : EReal) - ∫⁻ x, v x ∂(μ.prod ν) =
      ∫⁻ x, ∫⁻ y, u (x, y) ∂ν ∂μ - ∫⁻ x, ∫⁻ y, v (x, y) ∂ν ∂μ := by
    rw [lintegral_prod _ (by fun_prop), lintegral_prod _ (by fun_prop)]
  convert h_u_v using 1
  · exact congrArg (eintegral (μ.prod ν)) hf_eq.symm
  · convert eintegral_coe_ennreal_sub _ _ _ using 1
    · congr! 2
      rw [eintegral]
      grind
    · exact hu_aemeasurable.lintegral_prod_right'
    · refine AEMeasurable.lintegral_prod_right ?_
      convert hv_aemeasurable using 1
      grind
    · cases hf_int with
      | inl h => left; convert h; rw [lintegral_prod _ (by fun_prop)]
      | inr h => right; convert h; rw [lintegral_prod _ (by fun_prop)]

lemma eintegral_prod_symm {β : Type*} {mβ : MeasurableSpace β} [SFinite μ]
    {ν : Measure β} [SFinite ν]
    (f : α × β → EReal) (hf : AEMeasurable f (μ.prod ν)) (hf_int : EIntegrable f (μ.prod ν)) :
    ∫ᵉ z, f z ∂(μ.prod ν) = ∫ᵉ y, ∫ᵉ x, f (x, y) ∂μ ∂ν := by
  calc ∫ᵉ z, f z ∂(μ.prod ν)
  _ = ∫ᵉ z, (f ∘ Prod.swap) z ∂(ν.prod μ) := by
    simp only [Function.comp_apply]
    rw [← eintegral_map' _ measurable_swap.aemeasurable, Measure.prod_swap]
    rwa [Measure.prod_swap]
  _ = ∫ᵉ y, ∫ᵉ x, (f ∘ Prod.swap) (y, x) ∂μ ∂ν := by
    rw [eintegral_prod]
    · refine AEMeasurable.comp_aemeasurable ?_ (by fun_prop)
      rwa [Measure.prod_swap]
    · convert hf_int using 1
      -- TODO: extract lemma EIntegrable.swap
      unfold MeasureTheory.EIntegrable
      simp only [Function.comp_apply, ne_eq]
      rw [lintegral_prod_swap (ν := ν) (fun p ↦ (f p).toENNReal),
        lintegral_prod_swap (ν := ν) (fun p ↦ (-f p).toENNReal)]
  _ = ∫ᵉ y, ∫ᵉ x, f (x, y) ∂μ ∂ν := by simp

end MeasureTheory
