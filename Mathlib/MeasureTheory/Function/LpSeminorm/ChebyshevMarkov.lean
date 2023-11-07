import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

open ENNReal

namespace MeasureTheory

variable {α E : Type*} [NormedAddCommGroup E] {m : MeasurableSpace α} (μ : Measure α) {p : ℝ≥0∞}

theorem pow_mul_meas_ge_le_snorm {f : α → E} (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞)
    (hf : AEStronglyMeasurable f μ) (ε : ℝ≥0∞) :
    (ε * μ { x | ε ≤ (‖f x‖₊ : ℝ≥0∞) ^ p.toReal }) ^ (1 / p.toReal) ≤ snorm f p μ := by
  rw [snorm_eq_lintegral_rpow_nnnorm hp_ne_zero hp_ne_top]
  exact ENNReal.rpow_le_rpow (mul_meas_ge_le_lintegral₀ (hf.ennnorm.pow_const _) ε)
    (one_div_nonneg.2 ENNReal.toReal_nonneg)
#align measure_theory.pow_mul_meas_ge_le_snorm MeasureTheory.pow_mul_meas_ge_le_snorm

theorem mul_meas_ge_le_pow_snorm {f : α → E} (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞)
    (hf : AEStronglyMeasurable f μ) (ε : ℝ≥0∞) :
    ε * μ { x | ε ≤ (‖f x‖₊ : ℝ≥0∞) ^ p.toReal } ≤ snorm f p μ ^ p.toReal := by
  have : 1 / p.toReal * p.toReal = 1 := by
    refine' one_div_mul_cancel _
    rw [Ne, ENNReal.toReal_eq_zero_iff]
    exact not_or_of_not hp_ne_zero hp_ne_top
  rw [← ENNReal.rpow_one (ε * μ { x | ε ≤ (‖f x‖₊ : ℝ≥0∞) ^ p.toReal }), ← this, ENNReal.rpow_mul]
  exact
    ENNReal.rpow_le_rpow (pow_mul_meas_ge_le_snorm μ hp_ne_zero hp_ne_top hf ε)
      ENNReal.toReal_nonneg
#align measure_theory.mul_meas_ge_le_pow_snorm MeasureTheory.mul_meas_ge_le_pow_snorm

/-- A version of Markov's inequality using Lp-norms. -/
theorem mul_meas_ge_le_pow_snorm' {f : α → E} (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞)
    (hf : AEStronglyMeasurable f μ) (ε : ℝ≥0∞) :
    ε ^ p.toReal * μ { x | ε ≤ ‖f x‖₊ } ≤ snorm f p μ ^ p.toReal := by
  convert mul_meas_ge_le_pow_snorm μ hp_ne_zero hp_ne_top hf (ε ^ p.toReal) using 4
  ext x
  rw [ENNReal.rpow_le_rpow_iff (ENNReal.toReal_pos hp_ne_zero hp_ne_top)]
#align measure_theory.mul_meas_ge_le_pow_snorm' MeasureTheory.mul_meas_ge_le_pow_snorm'

theorem meas_ge_le_mul_pow_snorm {f : α → E} (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞)
    (hf : AEStronglyMeasurable f μ) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    μ { x | ε ≤ ‖f x‖₊ } ≤ ε⁻¹ ^ p.toReal * snorm f p μ ^ p.toReal := by
  by_cases ε = ∞
  · simp [h]
  have hεpow : ε ^ p.toReal ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.2 hε) h).ne.symm
  have hεpow' : ε ^ p.toReal ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg h
  rw [ENNReal.inv_rpow, ← ENNReal.mul_le_mul_left hεpow hεpow', ← mul_assoc,
    ENNReal.mul_inv_cancel hεpow hεpow', one_mul]
  exact mul_meas_ge_le_pow_snorm' μ hp_ne_zero hp_ne_top hf ε
#align measure_theory.meas_ge_le_mul_pow_snorm MeasureTheory.meas_ge_le_mul_pow_snorm

