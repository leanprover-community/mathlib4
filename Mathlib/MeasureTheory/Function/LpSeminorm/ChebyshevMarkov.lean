/-
Copyright (c) 2022 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

#align_import measure_theory.function.lp_seminorm from "leanprover-community/mathlib"@"c4015acc0a223449d44061e27ddac1835a3852b9"

/-!
# Chebyshev-Markov inequality in terms of Lp seminorms

In this file we formulate several versions of the Chebyshev-Markov inequality
in terms of the `MeasureTheory.snorm` seminorm.
-/
open scoped ENNReal

namespace MeasureTheory

variable {α E : Type*} {m0 : MeasurableSpace α} [NormedAddCommGroup E]
  {p : ℝ≥0∞} (μ : Measure α) {f : α → E}

theorem pow_mul_meas_ge_le_snorm (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞)
    (hf : AEStronglyMeasurable f μ) (ε : ℝ≥0∞) :
    (ε * μ { x | ε ≤ (‖f x‖₊ : ℝ≥0∞) ^ p.toReal }) ^ (1 / p.toReal) ≤ snorm f p μ := by
  rw [snorm_eq_lintegral_rpow_nnnorm hp_ne_zero hp_ne_top]
  gcongr
  exact mul_meas_ge_le_lintegral₀ (hf.ennnorm.pow_const _) ε
#align measure_theory.pow_mul_meas_ge_le_snorm MeasureTheory.pow_mul_meas_ge_le_snorm

theorem mul_meas_ge_le_pow_snorm (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞)
    (hf : AEStronglyMeasurable f μ) (ε : ℝ≥0∞) :
    ε * μ { x | ε ≤ (‖f x‖₊ : ℝ≥0∞) ^ p.toReal } ≤ snorm f p μ ^ p.toReal := by
  have : 1 / p.toReal * p.toReal = 1 := by
    refine one_div_mul_cancel ?_
    rw [Ne, ENNReal.toReal_eq_zero_iff]
    exact not_or_of_not hp_ne_zero hp_ne_top
  rw [← ENNReal.rpow_one (ε * μ { x | ε ≤ (‖f x‖₊ : ℝ≥0∞) ^ p.toReal }), ← this, ENNReal.rpow_mul]
  gcongr
  exact pow_mul_meas_ge_le_snorm μ hp_ne_zero hp_ne_top hf ε
#align measure_theory.mul_meas_ge_le_pow_snorm MeasureTheory.mul_meas_ge_le_pow_snorm

/-- A version of Chebyshev-Markov's inequality using Lp-norms. -/
theorem mul_meas_ge_le_pow_snorm' (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞)
    (hf : AEStronglyMeasurable f μ) (ε : ℝ≥0∞) :
    ε ^ p.toReal * μ { x | ε ≤ ‖f x‖₊ } ≤ snorm f p μ ^ p.toReal := by
  convert mul_meas_ge_le_pow_snorm μ hp_ne_zero hp_ne_top hf (ε ^ p.toReal) using 4
  ext x
  rw [ENNReal.rpow_le_rpow_iff (ENNReal.toReal_pos hp_ne_zero hp_ne_top)]
#align measure_theory.mul_meas_ge_le_pow_snorm' MeasureTheory.mul_meas_ge_le_pow_snorm'

theorem meas_ge_le_mul_pow_snorm (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞)
    (hf : AEStronglyMeasurable f μ) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    μ { x | ε ≤ ‖f x‖₊ } ≤ ε⁻¹ ^ p.toReal * snorm f p μ ^ p.toReal := by
  by_cases h : ε = ∞
  · simp [h]
  have hεpow : ε ^ p.toReal ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.2 hε) h).ne.symm
  have hεpow' : ε ^ p.toReal ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg h
  rw [ENNReal.inv_rpow, ← ENNReal.mul_le_mul_left hεpow hεpow', ← mul_assoc,
    ENNReal.mul_inv_cancel hεpow hεpow', one_mul]
  exact mul_meas_ge_le_pow_snorm' μ hp_ne_zero hp_ne_top hf ε
#align measure_theory.meas_ge_le_mul_pow_snorm MeasureTheory.meas_ge_le_mul_pow_snorm
