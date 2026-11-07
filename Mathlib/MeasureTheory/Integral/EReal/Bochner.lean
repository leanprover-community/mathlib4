/-
Copyright (c) 2025 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré, Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.EReal.EIntegral
public import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Extended integral and Bochner integral

We compare the integral `∫ᵉ` of `EReal`-valued functions with the Bochner integral of real-valued
functions.

## Main statements

* `eintegral_eq_integral`: for an integrable function `f : α → ℝ`, the extended integral of `f`
  (coerced to `EReal`) is its Bochner integral.
* `integrable_toReal_of_eintegral_ne_bot_of_ne_top`: if the extended integral of
  `f : α → EReal` is finite, then `fun x ↦ (f x).toReal` is integrable.
* `eintegral_eq_integral_toReal`: if the extended integral of `f : α → EReal` is finite, then it
  is equal to the Bochner integral of `fun x ↦ (f x).toReal`.

-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α} {f : α → EReal}

/-- For `Integrable` real-valued functions, the extended integral coincides with the
Bochner integral. -/
lemma eintegral_eq_integral {f : α → ℝ} (hf : Integrable f μ) :
    ∫ᵉ x, f x ∂μ = ∫ x, f x ∂μ := by
  have h_pos : ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≠ ∞ := hf.lintegral_lt_top.ne
  have h_neg : ∫⁻ x, ENNReal.ofReal (-f x) ∂μ ≠ ∞ := hf.neg.lintegral_lt_top.ne
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hf, eintegral]
  simp only [← EReal.coe_neg, EReal.toENNReal_of_ne_top (EReal.coe_ne_top _), EReal.toReal_coe]
  rw [← EReal.coe_ennreal_toReal h_pos, ← EReal.coe_ennreal_toReal h_neg, EReal.coe_sub]

lemma integrable_toReal_of_eintegral_ne_bot_of_ne_top (hf_meas : AEMeasurable f μ)
    (hf_bot : ∫ᵉ x, f x ∂μ ≠ ⊥) (hf_top : ∫ᵉ x, f x ∂μ ≠ ⊤) :
    Integrable (fun x ↦ (f x).toReal) μ := by
  simp_rw [← EReal.toReal_toENNReal_sub_toReal_toENNReal_neg]
  exact (integrable_toReal_of_lintegral_ne_top (by fun_prop)
      (lintegral_toENNReal_ne_top_of_eintegral_ne_top (eintegrable_of_eintegral_ne_bot hf_bot)
        hf_top)).sub
    (integrable_toReal_of_lintegral_ne_top (by fun_prop)
      (lintegral_toENNReal_neg_ne_top_of_eintegral_ne_bot hf_bot))

/-- For an almost everywhere finite function `f`, the function `fun x ↦ (f x).toReal` is integrable
if and only if the extended integral of `f` is finite. -/
lemma integrable_toReal_iff_eintegral_ne_bot_and_ne_top (hf_meas : AEMeasurable f μ)
    (hf_bot : ∀ᵐ x ∂μ, f x ≠ ⊥) (hf_top : ∀ᵐ x ∂μ, f x ≠ ⊤) :
    Integrable (fun x ↦ (f x).toReal) μ ↔ ∫ᵉ x, f x ∂μ ≠ ⊥ ∧ ∫ᵉ x, f x ∂μ ≠ ⊤ := by
  refine ⟨fun h ↦ ?_, fun h ↦ integrable_toReal_of_eintegral_ne_bot_of_ne_top hf_meas h.1 h.2⟩
  have h_eq : ∀ᵐ x ∂μ, f x = (f x).toReal := by
    filter_upwards [hf_bot, hf_top] with x hx_bot hx_top
    rw [EReal.coe_toReal hx_top hx_bot]
  rw [eintegral_congr_ae h_eq, eintegral_eq_integral h]
  simp

/-- If the extended integral of `f` is finite, then it equals the Bochner integral of
`fun x ↦ (f x).toReal`. -/
lemma eintegral_eq_integral_toReal (hf_meas : AEMeasurable f μ) (hf_bot : ∫ᵉ x, f x ∂μ ≠ ⊥)
    (hf_top : ∫ᵉ x, f x ∂μ ≠ ⊤) :
    ∫ᵉ x, f x ∂μ = ∫ x, (f x).toReal ∂μ := by
  have h_eq : ∀ᵐ x ∂μ, f x = (f x).toReal := by
    filter_upwards [ae_ne_bot_of_eintegral_ne_bot hf_meas hf_bot,
      ae_ne_top_of_eintegral_ne_top hf_meas (eintegrable_of_eintegral_ne_bot hf_bot) hf_top]
      with x hx_bot hx_top
    rw [EReal.coe_toReal hx_top hx_bot]
  rw [eintegral_congr_ae h_eq,
    eintegral_eq_integral (integrable_toReal_of_eintegral_ne_bot_of_ne_top hf_meas hf_bot hf_top)]

end MeasureTheory
