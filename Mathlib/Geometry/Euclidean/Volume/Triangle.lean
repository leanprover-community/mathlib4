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
* `Affine.Triangle.volume_eq_mul_sin`: $S = \frac{1}{2}ab \sin C$
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
    letI a := dist p₁ p₂
    letI b := dist p₁ p₃
    letI c := dist p₂ p₃
    letI s := (a + b + c) / 2
    2⁻¹ * a * c * sin (∠ p₁ p₂ p₃) = √(s * (s - a) * (s - b) * (s - c)) := by
  set a := dist p₁ p₂
  set b := dist p₁ p₃
  set c := dist p₂ p₃
  have h_cos : b * b = a * a + c * c - 2 * a * c * cos (∠ p₁ p₂ p₃) := by
    simpa only [dist_comm p₃ p₂] using law_cos p₁ p₂ p₃
  have h_sin : 0 ≤ sin (∠ p₁ p₂ p₃) :=
    sin_nonneg_of_nonneg_of_le_pi (angle_nonneg ..) (angle_le_pi ..)
  rw [← sqrt_sq (by positivity : 0 ≤ 2⁻¹ * a * c * sin (∠ p₁ p₂ p₃))]
  congr 1
  linear_combination (-2 * a * c * cos (∠ p₁ p₂ p₃) - a * a - c * c + b * b) / 16 * h_cos +
    a ^ 2 * c ^ 2 / 4 * sin_sq_add_cos_sq (∠ p₁ p₂ p₃)

include h₁₂ h₁₃ h₂₃ in
/-- **Heron's formula** for triangle. The area of a triangle with side lengths
`a`, `b`, and `c` is `√(s * (s - a) * (s - b) * (s - c))` where `s = (a + b + c) / 2` is the
semiperimeter. -/
theorem volume_eq_sqrt_mul_sub_mul_sub_mul_sub :
    letI a := dist (t.points i₁) (t.points i₂)
    letI b := dist (t.points i₁) (t.points i₃)
    letI c := dist (t.points i₂) (t.points i₃)
    letI s := (a + b + c) / 2
    t.volume = √(s * (s - a) * (s - b) * (s - c)) := by
  rw [t.volume_eq_mul_sin h₁₂ h₁₃ h₂₃, mul_sin_eq_sqrt_mul_sub_mul_sub_mul_sub]

include h₁₂ h₁₃ h₂₃ in
theorem volume_sq_eq_mul_sub_mul_sub_mul_sub :
    letI a := dist (t.points i₁) (t.points i₂)
    letI b := dist (t.points i₁) (t.points i₃)
    letI c := dist (t.points i₂) (t.points i₃)
    letI s := (a + b + c) / 2
    t.volume ^ 2 = s * (s - a) * (s - b) * (s - c) := by
  rw [t.volume_eq_sqrt_mul_sub_mul_sub_mul_sub h₁₂ h₁₃ h₂₃, sq_sqrt]
  by_contra! h
  have := sqrt_eq_zero_of_nonpos h.le
  rw [← t.volume_eq_sqrt_mul_sub_mul_sub_mul_sub h₁₂ h₁₃ h₂₃] at this
  simp [t.volume_pos.ne'] at this

end Affine.Triangle
