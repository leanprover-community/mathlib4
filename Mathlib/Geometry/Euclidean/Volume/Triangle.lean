/-
Copyright (c) 2026 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import Mathlib.Geometry.Euclidean.Triangle
public import Mathlib.Geometry.Euclidean.Volume.Basic

/-!
# Area of a triangle

This file collects formula for the area of a triangle and other related results.

## Main theorems

* `Affine.Triangle.volume_eq_height_mul`: $S = \frac{1}{2}hb$
* `Affine.Triangle.volume_eq_mul_sin`: $S = \frac{1}{2}ab \sin C$
-/

public section

namespace Affine.Triangle

open Simplex EuclideanGeometry

variable {V P : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
variable (t : Triangle ℝ P) {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃)

include h₁₂ h₁₃ h₂₃ in
theorem volume_eq_height_mul : t.volume = 2⁻¹ * t.height i₁ * dist (t.points i₂) (t.points i₃) := by
  let e : Fin 3 ≃ Fin 3 := {
    toFun x := if x = i₁ then 0 else if x = i₂ then 1 else 2
    invFun := ![i₁, i₂, i₃]
    left_inv x := by fin_cases x <;> fin_cases i₁ <;> fin_cases i₂ <;> simp <;> grind
    right_inv x := by fin_cases x <;> simp <;> grind
  }
  let s := t.reindex e
  suffices s.volume = 2⁻¹ * s.height 0 * dist (s.points 1) (s.points 2) by
    simpa [e, s] using this
  simp [s.volume_eq 0, volume_eq_dist, faceOpposite_point_eq_point_succAbove]

include h₁₂ h₁₃ h₂₃ in
theorem volume_eq_mul_sin :
    t.volume = 2⁻¹ * dist (t.points i₁) (t.points i₂) * dist (t.points i₂) (t.points i₃) *
      Real.sin (∠ (t.points i₁) (t.points i₂) (t.points i₃)) := by
  rw [t.volume_eq_height_mul h₁₂ h₁₃ h₂₃, t.height_eq_dist_mul_sin h₁₂ h₁₃ h₂₃]
  ring

end Affine.Triangle
