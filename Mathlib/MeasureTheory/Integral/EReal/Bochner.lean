/-
Copyright (c) 2025 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré, Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.EReal.EIntegral

/-!
# TODO

-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α} {f g : α → EReal}

/-- For `Integrable` real-valued functions, the extended integral coincides with the
standard Bochner integral. -/
lemma eintegral_eq_integral {f : α → ℝ} (hf : Integrable f μ) :
    ∫ᵉ x, f x ∂μ = ∫ x, f x ∂μ := by
  rw [eintegral_eq_posPartFun_sub_negPartFun, eintegral_of_nonneg (by simp),
    eintegral_of_nonneg (by simp)]
  simp only [posPart_def, Pi.sup_apply, Pi.zero_apply, ne_eq, max_eq_top, EReal.coe_ne_top,
    EReal.zero_ne_top, or_self, not_false_eq_true, EReal.toENNReal_of_ne_top, negPart_def,
    Pi.neg_apply, EReal.neg_eq_top_iff, EReal.coe_ne_bot]
  have h_int_max : Integrable (fun x ↦ (max (f x : EReal) 0).toReal) μ := by
    refine hf.mono ?_ ?_
    · exact AEMeasurable.aestronglyMeasurable (by fun_prop)
    · filter_upwards with x
      rcases le_total 0 (f x) with h | h <;> simp [h]
  have h_int_min : Integrable (fun x ↦ (max (- f x : EReal) 0).toReal) μ := by
    refine hf.mono ?_ ?_
    · exact AEMeasurable.aestronglyMeasurable (by fun_prop)
    · filter_upwards with x
      rcases le_total 0 (f x) with h | h <;> simp [h]
  rw [← ofReal_integral_eq_lintegral_ofReal, ← ofReal_integral_eq_lintegral_ofReal]
  rotate_left
  · exact h_int_min
  · filter_upwards with x
    simp only [Pi.zero_apply]
    rw [← EReal.toReal_zero]
    exact EReal.toReal_le_toReal (by simp) (by simp) (by simp)
  · exact h_int_max
  · filter_upwards with x
    simp only [Pi.zero_apply]
    rw [← EReal.toReal_zero]
    exact EReal.toReal_le_toReal (by simp) (by simp) (by simp)
  simp only [EReal.coe_ennreal_ofReal]
  rw [max_eq_left, max_eq_left]
  rotate_left
  · exact integral_nonneg fun x ↦ by rcases le_total 0 (f x) with h | h <;> simp [h]
  · exact integral_nonneg fun x ↦ by rcases le_total 0 (f x) with h | h <;> simp [h]
  norm_cast
  rw [← integral_sub]
  rotate_left
  · exact h_int_max
  · exact h_int_min
  congr with x
  rcases le_total 0 (f x) with h | h <;> simp [h]

lemma EReal.enorm_ereal_toReal {x : EReal} (h_top : x ≠ ⊤) (h_bot : x ≠ ⊥) :
    ‖x.toReal‖ₑ = ‖x‖ₑ := by
  lift x to ℝ using ⟨h_top, h_bot⟩ with r
  simp only [enorm, nnnorm, EReal.toReal_coe, Real.norm_eq_abs, abs, posPart_def, ne_eq, max_eq_top,
    EReal.coe_ne_top, EReal.zero_ne_top, or_self, not_false_eq_true, EReal.toENNReal_of_ne_top,
    negPart_def, EReal.neg_eq_top_iff, EReal.coe_ne_bot]
  rcases le_total 0 r with h | h <;> simp [ENNReal.ofReal, Real.toNNReal, h]

lemma lintegral_enorm_ereal_toReal (hf_ne_bot : ∀ᵐ x ∂μ, f x ≠ ⊥) (hf_ne_top : ∀ᵐ x ∂μ, f x ≠ ⊤) :
    ∫⁻ a, ‖(f a).toReal‖ₑ ∂μ = ∫⁻ a, ‖f a‖ₑ ∂μ := by
  refine lintegral_congr_ae ?_
  filter_upwards [hf_ne_bot, hf_ne_top] with x hfx_ne_bot hfx_ne_top
  rw [EReal.enorm_ereal_toReal hfx_ne_top hfx_ne_bot]

lemma integrable_toReal (hf_meas : AEMeasurable f μ) (h_int_bot : ∫ᵉ x, f x ∂μ ≠ ⊥)
    (h_int_top : ∫ᵉ x, f x ∂μ ≠ ⊤) :
    Integrable (fun x ↦ (f x).toReal) μ := by
  refine ⟨AEMeasurable.aestronglyMeasurable <| by fun_prop, ?_⟩
  rw [HasFiniteIntegral]
  suffices (∫⁻ a, ‖(f a).toReal‖ₑ ∂μ : EReal) < ⊤ by
    simp only [lt_top_iff_ne_top, ne_eq, EReal.coe_ennreal_eq_top_iff] at this
    rwa [lt_top_iff_ne_top]
  have h_eq : ∫⁻ a, ‖(f a).toReal‖ₑ ∂μ = ∫⁻ a, ‖f a‖ₑ ∂μ := by
    have hf_ne_bot : ∀ᵐ x ∂μ, f x ≠ ⊥ := ae_ne_bot_of_eintegral_ne_bot hf_meas h_int_bot
    have hf_ne_top : ∀ᵐ x ∂μ, f x ≠ ⊤ := ae_ne_top_of_eintegral_ne_top hf_meas h_int_bot h_int_top
    exact lintegral_enorm_ereal_toReal hf_ne_bot hf_ne_top
  rw [h_eq, lintegral_enorm_eq_posPartFun_add_negPartFun hf_meas]
  refine EReal.add_lt_top ?_ ?_
  · exact eintegral_posPartFun_ne_top h_int_bot h_int_top
  · exact eintegral_negPartFun_ne_top h_int_bot

lemma integrable_ereal_toReal_iff (hf_meas : AEMeasurable f μ)
    (h_bot : ∀ᵐ x ∂μ, f x ≠ ⊥) (h_top : ∀ᵐ x ∂μ, f x ≠ ⊤) :
    Integrable (fun x ↦ (f x).toReal) μ ↔ ∫ᵉ x, f x ∂μ ≠ ⊥ ∧ ∫ᵉ x, f x ∂μ ≠ ⊤ := by
  refine ⟨fun h ↦ ?_, fun ⟨h1, h2⟩ ↦ integrable_toReal hf_meas h1 h2⟩
  have h_lintegral : ∫⁻ a, ‖(f a).toReal‖ₑ ∂μ < ∞ := h.hasFiniteIntegral
  rw [lintegral_enorm_ereal_toReal h_bot h_top] at h_lintegral
  rw [eintegral_eq_posPartFun_sub_negPartFun]
  have := lintegral_enorm_eq_posPartFun_add_negPartFun hf_meas
  have h_pos_ne_bot : ∫ᵉ x, f⁺ x ∂μ ≠ ⊥ := by simp [eintegral_of_nonneg (posPart_fun_nonneg _)]
  have h_neg_ne_bot : ∫ᵉ x, f⁻ x ∂μ ≠ ⊥ := by simp [eintegral_of_nonneg (negPart_fun_nonneg _)]
  have h_pos_ne_top : ∫ᵉ x, f⁺ x ∂μ ≠ ⊤ := by
    intro h_contra
    simp only [h_contra] at this
    rw [EReal.top_add_of_ne_bot h_neg_ne_bot] at this
    simp_all
  have h_neg_ne_top : ∫ᵉ x, f⁻ x ∂μ ≠ ⊤ := by
    intro h_contra
    simp only [h_contra] at this
    rw [EReal.add_top_of_ne_bot h_pos_ne_bot] at this
    simp_all
  lift ∫ᵉ x, f⁺ x ∂μ to ℝ using ⟨h_pos_ne_top, h_pos_ne_bot⟩ with int_pos
  lift ∫ᵉ x, f⁻ x ∂μ to ℝ using ⟨h_neg_ne_top, h_neg_ne_bot⟩ with int_neg
  norm_cast
  simp only [EReal.coe_ne_bot, EReal.coe_ne_top, not_false_eq_true, and_true]

/-- If the extended integral is finite, then it equals the integral of the real part. -/
lemma eintegral_eq_integral_toReal (hf_meas : AEMeasurable f μ) (h_int_bot : ∫ᵉ x, f x ∂μ ≠ ⊥)
    (h_int_top : ∫ᵉ x, f x ∂μ ≠ ⊤) :
    ∫ᵉ x, f x ∂μ = ∫ x, (f x).toReal ∂μ := by
  have hf_ne_bot : ∀ᵐ x ∂μ, f x ≠ ⊥ := ae_ne_bot_of_eintegral_ne_bot hf_meas h_int_bot
  have hf_ne_top : ∀ᵐ x ∂μ, f x ≠ ⊤ := ae_ne_top_of_eintegral_ne_top hf_meas h_int_bot h_int_top
  have hf_eq : ∀ᵐ x ∂μ, f x = (f x).toReal := by
    filter_upwards [hf_ne_bot, hf_ne_top] with x hx_bot hx_top
    rw [EReal.coe_toReal hx_top hx_bot]
  rw [eintegral_congr_ae hf_eq, eintegral_eq_integral]
  exact integrable_toReal hf_meas h_int_bot h_int_top

end MeasureTheory
