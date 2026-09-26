/-
Copyright (c) 2026 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang, Matt Kempster
-/
module

public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
public import Mathlib.Geometry.Euclidean.Circumcenter
public import Mathlib.Geometry.Euclidean.NinePointCircle
public import Mathlib.Geometry.Euclidean.Volume.Incenter

import Mathlib.Geometry.Euclidean.Angle.Sphere
import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Geometry.Euclidean.Volume.Basic

/-!
# Area of a triangle

This file collects formulas for the area of a triangle and other related results.

## Main theorems

* `Affine.Triangle.volume_eq_height_mul`: $S = \frac{1}{2}hb$
* `Affine.Triangle.volume_eq_mul_sin`: $S = \frac{1}{2}ab \sin C$3
* `Affine.Triangle.volume_eq_sqrt_mul_sub_mul_sub_mul_sub`: Heron's formula.
* `Affine.Triangle.volume_eq_mul_div_circumradius`: $S = abc/(4R)$ where $R$ is the circumradius.
* `Affine.Triangle.dist_excenter_singleton_circumcenter_sq`:
  Euler's theorem in geometry for excenter.
* `Affine.Triangle.dist_incenter_circumcenter_sq`: Euler's theorem in geometry for incenter.
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

include h₁₂ h₁₃ h₂₃ in
/-- Triangle area is equal to $abc / (4R)$, where $a$, $b$, and $c$ are side length and $R$ is the
circumradius. -/
theorem volume_eq_mul_div_circumradius :
    t.volume = dist (t.points i₁) (t.points i₂) * dist (t.points i₁) (t.points i₃) *
      dist (t.points i₂) (t.points i₃) / (4 * t.circumradius) := by
  have : dist (t.points i₁) (t.points i₃) ≠ 0 := by simpa using t.independent.injective.ne h₁₃
  rw [t.volume_eq_mul_sin h₁₂ h₁₃ h₂₃, ← t.dist_div_sin_angle_div_two_eq_circumradius h₁₂ h₁₃ h₂₃]
  field

include h₁₂ h₁₃ h₂₃ in
theorem four_mul_volume_mul_circumradius :
    4 * t.volume * t.circumradius = dist (t.points i₁) (t.points i₂) *
      dist (t.points i₁) (t.points i₃) * dist (t.points i₂) (t.points i₃) := by
  have : t.circumradius ≠ 0 := t.circumradius_pos.ne'
  simp [t.volume_eq_mul_div_circumradius h₁₂ h₁₃ h₂₃, field]

local notation "w" => excenterWeightsFace

theorem sum_excenterWeightsFace_pos {signs : Finset (Fin 3)}
    (hsigns : signs = ∅ ∨ signs = {0} ∨ signs = {1} ∨ signs = {2}) :
    0 < ∑ i, w t signs i := by
  rcases hsigns with rfl | hsigns
  · refine Finset.sum_pos (fun i _ ↦ ?_) (by simp)
    simp [faceOpposite_point_eq_point_succAbove, t.independent.injective.ne]
  · rcases hsigns with rfl | rfl | rfl <;> apply sum_excenterWeightsFace_singleton_pos

theorem dist_excenter_sq (p : P) {signs : Finset (Fin 3)}
    (hsigns : signs = ∅ ∨ signs = {0} ∨ signs = {1} ∨ signs = {2}) :
    dist (t.excenter signs) p ^ 2 = ∑ i, t.excenterWeights signs i * dist (t.points i) p ^ 2 +
      (if signs = ∅ then -1 else 1) * 2 * t.circumradius * t.exradius signs := by
  have h0 := t.sum_excenterWeightsFace_pos hsigns
  rw [t.excenter_eq_affineCombination, dist_affineCombination_const_sq _ _
    (t.sum_excenterWeights_eq_one_iff.mpr (t.excenterExists _))]
  congrm _ + ?_
  calc
    _ = -((∑ i, ∑ j, w t signs i * w t signs j * dist (t.points i) (t.points j) ^ 2) / 2 /
        (∑ i, w t signs i) ^ 2) := by
      simp_rw [t.excenterWeights_eq_excenterWeightsFace_div, Finset.sum_div]
      congrm -∑ i, ∑ j, $(by ring)
    _ = (if signs = ∅ then -1 else 1) *
        (dist (t.points 0) (t.points 1) * dist (t.points 0) (t.points 2) *
        dist (t.points 1) (t.points 2)) * (∑ i, w t signs i) / (∑ i, w t signs i) ^ 2 := by
      have : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by grind
      rcases hsigns with rfl | rfl | rfl | rfl
      all_goals
      simp [this, excenterWeightsFace, faceOpposite_point_eq_point_succAbove,
        Fin.succAbove, dist_comm (t.points 1) (t.points 0), dist_comm (t.points 2) (t.points 1),
        dist_comm (t.points 2) (t.points 0)]
      ring
    _ = _ := by
      rw [← t.four_mul_volume_mul_circumradius (by simp) (by simp) (by simp),
        (t.excenterExists signs).volume_eq_exradius_mul, abs_of_nonneg h0.le]
      field

theorem dist_excenter_circumcenter_sq {signs : Finset (Fin 3)}
    (hsigns : signs = ∅ ∨ signs = {0} ∨ signs = {1} ∨ signs = {2}) :
    dist (t.excenter signs) t.circumcenter ^ 2 =
      t.circumradius * (t.circumradius + (if signs = ∅ then -1 else 1) * 2 * t.exradius signs) := by
  simp_rw [t.dist_excenter_sq t.circumcenter hsigns, dist_circumcenter_eq_circumradius,
    ← Finset.sum_mul, t.sum_excenterWeights_eq_one_iff.mpr (t.excenterExists _)]
  ring

/-- **Euler's theorem in geometry** for excenter. -/
theorem dist_excenter_singleton_circumcenter_sq (i : Fin 3) :
    dist (t.excenter {i}) t.circumcenter ^ 2 =
      t.circumradius * (t.circumradius + 2 * t.exradius {i}) := by
  rw [t.dist_excenter_circumcenter_sq (by grind)]
  simp

/-- **Euler's theorem in geometry** for incenter. -/
theorem dist_incenter_circumcenter_sq :
    dist t.incenter t.circumcenter ^ 2 = t.circumradius * (t.circumradius - 2 * t.inradius) := by
  rw [← excenter_empty, t.dist_excenter_circumcenter_sq (by grind)]
  simp [← sub_eq_add_neg]

/-- **Euler inequality**: the inradius of a triangle is not larger than half of the circumradius. -/
theorem two_mul_inradius_le_circumradius : 2 * t.inradius ≤ t.circumradius := by
  have := sq_nonneg (dist t.incenter t.circumcenter)
  rw [dist_incenter_circumcenter_sq] at this
  simpa using nonneg_of_mul_nonneg_right this (t.circumradius_pos)

theorem inradius_le_ninePointCircle_radius : t.inradius ≤ t.ninePointCircle.radius := by
  grw [ninePointCircle_radius, ← two_mul_inradius_le_circumradius]
  simp

end Affine.Triangle
