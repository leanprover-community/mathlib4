/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl
-/
module

public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

set_option doc.verso true
set_option doc.verso.suggestions false

/-!
# Interactions between the Lebesgue integral and norms
-/

public section

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem lintegral_ofReal_le_lintegral_eNorm (f : α → ℝ) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≤ ∫⁻ x, ‖f x‖ₑ ∂μ := by
  simp_rw [← ofReal_norm]
  refine lintegral_mono fun x => ENNReal.ofReal_le_ofReal ?_
  rw [Real.norm_eq_abs]
  exact le_abs_self (f x)

@[deprecated (since := "2026-11-06")]
alias lintegral_ofReal_le_lintegral_enorm := lintegral_ofReal_le_lintegral_eNorm

theorem lintegral_eNorm_of_ae_nonneg {f : α → ℝ} (h_nonneg : 0 ≤ᵐ[μ] f) :
    ∫⁻ x, ‖f x‖ₑ ∂μ = ∫⁻ x, .ofReal (f x) ∂μ := by
  apply lintegral_congr_ae
  filter_upwards [h_nonneg] with x hx
  rw [Real.eNorm_eq_ofReal hx]

@[deprecated (since := "2026-11-06")]
alias lintegral_enorm_of_ae_nonneg := lintegral_eNorm_of_ae_nonneg

theorem lintegral_eNorm_of_nonneg {f : α → ℝ} (h_nonneg : 0 ≤ f) :
    ∫⁻ x, ‖f x‖ₑ ∂μ = ∫⁻ x, .ofReal (f x) ∂μ :=
  lintegral_eNorm_of_ae_nonneg <| .of_forall h_nonneg

@[deprecated (since := "2026-11-06")] alias lintegral_enorm_of_nonneg := lintegral_eNorm_of_nonneg

end MeasureTheory
