/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Heather Macbeth
-/
import Mathlib.MeasureTheory.Integral.Bochner

/-!
A supplement to the file
# Bochner integral
-/

open ENNReal
set_option autoImplicit true
noncomputable section

namespace MeasureTheory

variable {α : Type*} {E : Type*}
  {_ : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

-- move to MeasureTheory.Function.L1Space
theorem Integrable.nnnorm_toL1 (f : α → E) (hf : Integrable f μ) :
    (‖hf.toL1 f‖₊ : ℝ≥0∞) = ∫⁻ a, ‖f a‖₊ ∂μ := by
  simpa [Integrable.toL1, snorm, snorm'] using ENNReal.coe_toNNReal hf.2.ne

theorem L1.nnnorm_Integral_le_one : ‖L1.integralCLM (α := α) (E := E) (μ := μ)‖₊ ≤ (1 : ℝ) :=
  L1.norm_Integral_le_one

theorem L1.nnnorm_integral_le (f : α →₁[μ] E) : ‖L1.integral f‖₊ ≤ ‖f‖₊ :=
  L1.norm_integral_le f

theorem nnnorm_integral_le_lintegral_nnnorm (f : α → E) :
    ‖∫ x, f x ∂μ‖₊ ≤ ∫⁻ x, ‖f x‖₊ ∂ μ := by
  rw [integral_def, dif_pos ‹_›]
  split_ifs with hf
  · calc _ ≤ (‖(Integrable.toL1 f hf)‖₊ : ℝ≥0∞) := by norm_cast; apply L1.nnnorm_integral_le
      _ = _ := hf.nnnorm_toL1
  · simp
