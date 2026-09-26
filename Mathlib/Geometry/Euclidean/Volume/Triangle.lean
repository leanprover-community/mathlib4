/-
Copyright (c) 2026 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang, Matt Kempster
-/
module

public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
public import Mathlib.Geometry.Euclidean.Volume.Def

import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Geometry.Euclidean.Volume.Basic

/-!
# Area of a triangle

This file collects formulas for the area of a triangle and other related results.

## Main theorems

* `Affine.Triangle.volume_eq_height_mul`: $S = \frac{1}{2}hb$
* `Affine.Triangle.volume_eq_mul_sin`: $S = \frac{1}{2}ab \sin C$3
* `Affine.Triangle.volume_eq_sqrt_mul_sub_mul_sub_mul_sub`: Heron's formula.
-/

public section

namespace Affine.Triangle

open Simplex EuclideanGeometry Real

variable {V P : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
variable (t : Triangle ℝ P) {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃)

include h₁₂ h₁₃ h₂₃ in
theorem volume_eq_height_mul : t.volume = 2⁻¹ * t.height i₁ * dist (t.points i₂) (t.points i₃) := by
  let e : Fin 3 ≃ Fin 3 := List.Nodup.getEquivOfForallMemList [i₁, i₂, i₃] (by grind) (by grind)
  let s := t.reindex e.symm
  suffices s.volume = 2⁻¹ * s.height 0 * dist (s.points 1) (s.points 2) by simpa [s]
  simp [s.volume_eq 0, volume_eq_dist, faceOpposite_point_eq_point_succAbove]

include h₁₂ h₁₃ h₂₃ in
theorem volume_eq_mul_sin :
    t.volume = 2⁻¹ * dist (t.points i₁) (t.points i₂) * dist (t.points i₂) (t.points i₃) *
      Real.sin (∠ (t.points i₁) (t.points i₂) (t.points i₃)) := by
  rw [t.volume_eq_height_mul h₁₂ h₁₃ h₂₃, t.height_eq_sin_mul_dist h₁₂ h₁₃ h₂₃]
  ring

/-- **Heron's formula** for possibly degenerate triangle. The area of a triangle with side lengths
`a`, `b`, and `c` is `√(s * (s - a) * (s - b) * (s - c))` where `s = (a + b + c) / 2` is the
semiperimeter. We show this by equating this formula to `2⁻¹ * a * c * sin γ`, where `γ` is the
angle opposite the side `b`. -/
theorem _root_.EuclideanGeometry.mul_sin_eq_sqrt_mul_sub_mul_sub_mul_sub (p₁ p₂ p₃ : P) :
    let a := dist p₁ p₂
    let b := dist p₁ p₃
    let c := dist p₂ p₃
    let s := (a + b + c) / 2
    2⁻¹ * a * c * sin (∠ p₁ p₂ p₃) = √(s * (s - a) * (s - b) * (s - c)) := by
  by_cases h1 : p₁ = p₂
  · simp [h1]
  by_cases h2 : p₂ = p₃
  · simp [h2]
  intro a b c s
  let γ := ∠ p₁ p₂ p₃
  obtain := (dist_pos.mpr h1).ne', (dist_pos.mpr h2).ne'
  have cos_rule : cos γ = (a * a + c * c - b * b) / (2 * a * c) := by
    simp [field, a, b, c, γ, mul_comm,
      dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle p₁ p₂ p₃,
      dist_comm p₃ p₂]
  let numerator := (2 * a * c) ^ 2 - (a * a + c * c - b * b) ^ 2
  let denominator := (2 * a * c) ^ 2
  have split_to_frac : 1 - cos γ ^ 2 = numerator / denominator := by
    simp [field, numerator, denominator, cos_rule]
  have numerator_nonneg : 0 ≤ numerator := by
    have frac_nonneg : 0 ≤ numerator / denominator :=
      (sub_nonneg.mpr (cos_sq_le_one γ)).trans_eq split_to_frac
    rcases div_nonneg_iff.mp frac_nonneg with h | h
    · exact h.left
    · simpa [numerator, denominator, a, b, c, h1, h2, dist_comm p₃ p₂]
        using le_antisymm h.right (sq_nonneg _)
  have ab2_nonneg : 0 ≤ 2 * a * c := by positivity
  calc
    2⁻¹ * a * c * sin γ = 1 / 2 * a * c * (√numerator / √denominator) := by
      rw [sin_eq_sqrt_one_sub_cos_sq, split_to_frac, sqrt_div numerator_nonneg] <;>
        simp [γ, angle_nonneg, angle_le_pi]
    _ = 1 / 4 * √((2 * a * b) ^ 2 - (a * a + b * b - c * c) ^ 2) := by
      simp (disch := positivity) [field, numerator, denominator, -mul_eq_mul_left_iff]; ring_nf
    _ = 1 / 4 * √(s * (s - a) * (s - b) * (s - c) * 4 ^ 2) := by simp only [s]; ring_nf
    _ = √(s * (s - a) * (s - b) * (s - c)) := by
      rw [sqrt_mul', sqrt_sq, div_mul_eq_mul_div, one_mul, mul_div_cancel_right₀] <;> norm_num

include h₁₂ h₁₃ h₂₃ in
/-- **Heron's formula** for triangle. The area of a triangle with side lengths
`a`, `b`, and `c` is `√(s * (s - a) * (s - b) * (s - c))` where `s = (a + b + c) / 2` is the
semiperimeter. -/
theorem volume_eq_sqrt_mul_sub_mul_sub_mul_sub :
    let a := dist (t.points i₁) (t.points i₂)
    let b := dist (t.points i₁) (t.points i₃)
    let c := dist (t.points i₂) (t.points i₃)
    let s := (a + b + c) / 2
    t.volume = √(s * (s - a) * (s - b) * (s - c)) := by
  rw [t.volume_eq_mul_sin h₁₂ h₁₃ h₂₃, mul_sin_eq_sqrt_mul_sub_mul_sub_mul_sub]

include h₁₂ h₁₃ h₂₃ in
theorem volume_sq_eq_mul_sub_mul_sub_mul_sub :
    let a := dist (t.points i₁) (t.points i₂)
    let b := dist (t.points i₁) (t.points i₃)
    let c := dist (t.points i₂) (t.points i₃)
    let s := (a + b + c) / 2
    t.volume ^ 2 = s * (s - a) * (s - b) * (s - c) := by
  rw [t.volume_eq_sqrt_mul_sub_mul_sub_mul_sub h₁₂ h₁₃ h₂₃, sq_sqrt]
  by_contra! h
  have := sqrt_eq_zero_of_nonpos h.le
  rw [← t.volume_eq_sqrt_mul_sub_mul_sub_mul_sub h₁₂ h₁₃ h₂₃] at this
  simp [t.volume_pos.ne'] at this

end Affine.Triangle
