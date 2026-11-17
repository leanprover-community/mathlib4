/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# Cubic Collar Majorants and Sine-Squared Definite Integral Bounds

This module defines the parametric cubic collar weight `(4 / (3 * p)) * δ ^ 3`, proves
non-negativity and antitonicity over linearly ordered fields, and proves the real definite
integral bound `(4 / π) * ∫ θ in 0..δ, sin θ ^ 2 ≤ cubicCollarWeight π δ`.

## Main results

- `CubicSinBounds.cubicCollarWeight`: parametric cubic weight `(4 / (3 * p)) * δ ^ 3`.
- `CubicSinBounds.cubicCollarWeight_nonneg`: non-negativity for `0 < p` and `0 ≤ δ`.
- `CubicSinBounds.cubicCollarWeight_anti_left`: antitonicity in the parameter `p`.
- `CubicSinBounds.sin_sq_le_sq`: pointwise bound `Real.sin θ ^ 2 ≤ θ ^ 2`.
- `CubicSinBounds.integral_sin_sq_le_cubic`: `∫ θ in 0..δ, sin θ ^ 2 ≤ δ ^ 3 / 3`.
- `CubicSinBounds.normalized_sin_sq_integral_le_cubicCollarWeight`: integral bound.
-/

@[expose] public section

namespace CubicSinBounds

section OrderedField

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- Parametric cubic collar weight `(4 / (3 * p)) * δ ^ 3`. -/
def cubicCollarWeight (p δ : F) : F :=
  (4 / (3 * p)) * δ ^ 3

/-- The cubic collar weight is non-negative when `0 < p` and `0 ≤ δ`. -/
theorem cubicCollarWeight_nonneg {p δ : F} (hp : 0 < p) (hδ : 0 ≤ δ) :
    0 ≤ cubicCollarWeight p δ := by
  unfold cubicCollarWeight
  positivity

/-- Antitonicity of `cubicCollarWeight` in its first argument: increasing `p` decreases
the collar weight when `0 < p₁ ≤ p₂` and `0 ≤ δ`. -/
theorem cubicCollarWeight_anti_left {p₁ p₂ δ : F}
    (hp₁ : 0 < p₁) (hp : p₁ ≤ p₂) (hδ : 0 ≤ δ) :
    cubicCollarWeight p₂ δ ≤ cubicCollarWeight p₁ δ := by
  unfold cubicCollarWeight
  have h3p₁ : 0 < 3 * p₁ := by positivity
  have h3p : 3 * p₁ ≤ 3 * p₂ := mul_le_mul_of_nonneg_left hp (by positivity)
  have hdiv : 4 / (3 * p₂) ≤ 4 / (3 * p₁) :=
    div_le_div_of_nonneg_left (by positivity) h3p₁ h3p
  exact mul_le_mul_of_nonneg_right hdiv (pow_nonneg hδ 3)

end OrderedField

section RealIntegral

/-- Pointwise bound `Real.sin θ ^ 2 ≤ θ ^ 2` for all `θ : ℝ`. -/
theorem sin_sq_le_sq (θ : ℝ) : Real.sin θ ^ 2 ≤ θ ^ 2 := by
  simpa [sq_abs] using sq_le_sq.mpr (Real.abs_sin_le_abs (x := θ))

/-- Definite integral cubic bound `∫ θ in 0..δ, Real.sin θ ^ 2 ≤ δ ^ 3 / 3` for `0 ≤ δ`. -/
theorem integral_sin_sq_le_cubic {δ : ℝ} (hδ : 0 ≤ δ) :
    (∫ θ in (0 : ℝ)..δ, Real.sin θ ^ 2) ≤ δ ^ 3 / 3 := by
  have hsin : IntervalIntegrable (fun θ => Real.sin θ ^ 2) MeasureTheory.volume 0 δ :=
    (Real.continuous_sin.pow 2).intervalIntegrable 0 δ
  have hsq : IntervalIntegrable (fun θ : ℝ => θ ^ 2) MeasureTheory.volume 0 δ :=
    (continuous_id.pow 2).intervalIntegrable 0 δ
  have hmono := intervalIntegral.integral_mono_on hδ hsin hsq (fun θ _ => sin_sq_le_sq θ)
  rw [integral_pow] at hmono
  linarith [show ((δ ^ (2 + 1) - (0 : ℝ) ^ (2 + 1)) / (↑(2 : ℕ) + 1)) = δ ^ 3 / 3 by norm_num]

/-- Normalized Weyl collar integral bound `(4 / π) * ∫ θ in 0..δ, sin θ ^ 2`
bounded by `cubicCollarWeight π δ` for `0 ≤ δ`. -/
theorem normalized_sin_sq_integral_le_cubicCollarWeight {δ : ℝ} (hδ : 0 ≤ δ) :
    (4 / Real.pi) * (∫ θ in (0 : ℝ)..δ, Real.sin θ ^ 2) ≤
      cubicCollarWeight Real.pi δ := by
  have hpi : (0 : ℝ) ≤ 4 / Real.pi := div_nonneg (by norm_num) Real.pi_pos.le
  have hmul := mul_le_mul_of_nonneg_left (integral_sin_sq_le_cubic hδ) hpi
  have heq : (4 / Real.pi) * (δ ^ 3 / 3) = cubicCollarWeight Real.pi δ := by
    unfold cubicCollarWeight
    ring
  rwa [heq] at hmul

end RealIntegral

end CubicSinBounds
