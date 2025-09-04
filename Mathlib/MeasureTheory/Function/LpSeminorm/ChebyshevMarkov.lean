/-
Copyright (c) 2022 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Chebyshev-Markov inequality in terms of Lp seminorms

In this file we formulate several versions of the Chebyshev-Markov inequality
in terms of the `MeasureTheory.eLpNorm` seminorm.
-/
open scoped NNReal ENNReal

namespace MeasureTheory

variable {α E ε' : Type*} {m0 : MeasurableSpace α} [NormedAddCommGroup E]
  [TopologicalSpace ε'] [ContinuousENorm ε']
  {p : ℝ≥0∞} (μ : Measure α)

theorem pow_mul_meas_ge_le_eLpNorm (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞)
    {f : α → ε'} (hf : AEStronglyMeasurable f μ) (ε : ℝ≥0∞) :
    (ε * μ { x | ε ≤ ‖f x‖ₑ ^ p.toReal }) ^ (1 / p.toReal) ≤ eLpNorm f p μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm hp_ne_zero hp_ne_top]
  gcongr
  exact mul_meas_ge_le_lintegral₀ (hf.enorm.pow_const _) ε

theorem mul_meas_ge_le_pow_eLpNorm (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞)
    {f : α → ε'} (hf : AEStronglyMeasurable f μ) (ε : ℝ≥0∞) :
    ε * μ { x | ε ≤ ‖f x‖ₑ ^ p.toReal } ≤ eLpNorm f p μ ^ p.toReal := by
  have : 1 / p.toReal * p.toReal = 1 := by
    refine one_div_mul_cancel ?_
    rw [Ne, ENNReal.toReal_eq_zero_iff]
    exact not_or_intro hp_ne_zero hp_ne_top
  rw [← ENNReal.rpow_one (ε * μ { x | ε ≤ ‖f x‖ₑ ^ p.toReal }), ← this, ENNReal.rpow_mul]
  gcongr
  exact pow_mul_meas_ge_le_eLpNorm μ hp_ne_zero hp_ne_top hf ε

/-- A version of Chebyshev-Markov's inequality using Lp-norms. -/
theorem mul_meas_ge_le_pow_eLpNorm' (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞)
    {f : α → ε'} (hf : AEStronglyMeasurable f μ) (ε : ℝ≥0∞) :
    ε ^ p.toReal * μ { x | ε ≤ ‖f x‖ₑ } ≤ eLpNorm f p μ ^ p.toReal := by
  convert mul_meas_ge_le_pow_eLpNorm μ hp_ne_zero hp_ne_top hf (ε ^ p.toReal) using 4
  ext x
  rw [ENNReal.rpow_le_rpow_iff (ENNReal.toReal_pos hp_ne_zero hp_ne_top)]

theorem meas_ge_le_mul_pow_eLpNorm_enorm (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞)
    {f : α → ε'} (hf : AEStronglyMeasurable f μ)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) (hmeas_top : ε = ∞ → μ {x | ‖f x‖ₑ = ⊤} = 0) :
    μ { x | ε ≤ ‖f x‖ₑ } ≤ ε⁻¹ ^ p.toReal * eLpNorm f p μ ^ p.toReal := by
  by_cases h : ε = ∞
  · have : (0 : ℝ≥0∞) ^ p.toReal = 0 := by
      rw [ENNReal.zero_rpow_of_pos (ENNReal.toReal_pos hp_ne_zero hp_ne_top)]
    simp [h, this, hmeas_top]
  · have hεpow : ε ^ p.toReal ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.2 hε) h).ne.symm
    have hεpow' : ε ^ p.toReal ≠ ∞ := by finiteness
    rw [ENNReal.inv_rpow, ← ENNReal.mul_le_mul_left hεpow hεpow', ← mul_assoc,
      ENNReal.mul_inv_cancel hεpow hεpow', one_mul]
    exact mul_meas_ge_le_pow_eLpNorm' μ hp_ne_zero hp_ne_top hf ε

theorem MemLp.meas_ge_lt_top'_enorm {μ : Measure α} {f : α → ε'} (hℒp : MemLp f p μ)
    (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) (hε' : ε = ∞ → μ {x | ‖f x‖ₑ = ⊤} = 0) :
    μ { x | ε ≤ ‖f x‖ₑ } < ∞ := by
  apply meas_ge_le_mul_pow_eLpNorm_enorm μ hp_ne_zero hp_ne_top hℒp.aestronglyMeasurable hε hε'
    |>.trans_lt (ENNReal.mul_lt_top ?_ ?_)
  · simp [hε, lt_top_iff_ne_top]
  · simp [hℒp.eLpNorm_lt_top.ne, lt_top_iff_ne_top]

theorem MemLp.meas_ge_lt_top' {μ : Measure α} {f : α → E} (hℒp : MemLp f p μ) (hp_ne_zero : p ≠ 0)
    (hp_ne_top : p ≠ ∞) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    μ { x | ε ≤ ‖f x‖₊ } < ∞ := by
  by_cases h : ε = ∞
  · simp [h]
  exact hℒp.meas_ge_lt_top'_enorm hp_ne_zero hp_ne_top hε (by simp)

theorem MemLp.meas_ge_lt_top_enorm {μ : Measure α} {f : α → ε'} (hℒp : MemLp f p μ)
    (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) {ε : ℝ≥0} (hε : ε ≠ 0) :
    μ { x | ε ≤ ‖f x‖ₑ } < ∞ :=
  hℒp.meas_ge_lt_top'_enorm hp_ne_zero hp_ne_top (by simp [hε]) (by simp)

theorem MemLp.meas_ge_lt_top {μ : Measure α} {f : α → E} (hℒp : MemLp f p μ) (hp_ne_zero : p ≠ 0)
    (hp_ne_top : p ≠ ∞) {ε : ℝ≥0} (hε : ε ≠ 0) :
    μ { x | ε ≤ ‖f x‖₊ } < ∞ := by
  simp_rw [← ENNReal.coe_le_coe]
  apply hℒp.meas_ge_lt_top' hp_ne_zero hp_ne_top (by simp [hε])

end MeasureTheory
