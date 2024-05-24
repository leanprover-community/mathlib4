/-
Copyright (c) 2021 Manuel Candales. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Candales, Benjamin Davidson
-/
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
import Mathlib.Geometry.Euclidean.Sphere.Basic

#align_import geometry.euclidean.sphere.power from "leanprover-community/mathlib"@"46b633fd842bef9469441c0209906f6dddd2b4f5"

/-!
# Power of a point (intersecting chords and secants)

This file proves basic geometrical results about power of a point (intersecting chords and
secants) in spheres in real inner product spaces and Euclidean affine spaces.

## Main theorems

* `mul_dist_eq_mul_dist_of_cospherical_of_angle_eq_pi`: Intersecting Chords Theorem (Freek No. 55).
* `mul_dist_eq_mul_dist_of_cospherical_of_angle_eq_zero`: Intersecting Secants Theorem.
-/


open Real

open EuclideanGeometry RealInnerProductSpace Real

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

namespace InnerProductGeometry

/-!
### Geometrical results on spheres in real inner product spaces

This section develops some results on spheres in real inner product spaces,
which are used to deduce corresponding results for Euclidean affine spaces.
-/


theorem mul_norm_eq_abs_sub_sq_norm {x y z : V} (h₁ : ∃ k : ℝ, k ≠ 1 ∧ x + y = k • (x - y))
    (h₂ : ‖z - y‖ = ‖z + y‖) : ‖x - y‖ * ‖x + y‖ = |‖z + y‖ ^ 2 - ‖z - x‖ ^ 2| := by
  obtain ⟨k, hk_ne_one, hk⟩ := h₁
  let r := (k - 1)⁻¹ * (k + 1)
  have hxy : x = r • y := by
    rw [← smul_smul, eq_inv_smul_iff₀ (sub_ne_zero.mpr hk_ne_one), ← sub_eq_zero]
    calc
      (k - 1) • x - (k + 1) • y = k • x - x - (k • y + y) := by
        simp_rw [sub_smul, add_smul, one_smul]
      _ = k • x - k • y - (x + y) := by simp_rw [← sub_sub, sub_right_comm]
      _ = k • (x - y) - (x + y) := by rw [← smul_sub k x y]
      _ = 0 := sub_eq_zero.mpr hk.symm
  have hzy : ⟪z, y⟫ = 0 := by
    rwa [inner_eq_zero_iff_angle_eq_pi_div_two, ← norm_add_eq_norm_sub_iff_angle_eq_pi_div_two,
      eq_comm]
  have hzx : ⟪z, x⟫ = 0 := by rw [hxy, inner_smul_right, hzy, mul_zero]
  calc
    ‖x - y‖ * ‖x + y‖ = ‖(r - 1) • y‖ * ‖(r + 1) • y‖ := by simp [sub_smul, add_smul, hxy]
    _ = ‖r - 1‖ * ‖y‖ * (‖r + 1‖ * ‖y‖) := by simp_rw [norm_smul]
    _ = ‖r - 1‖ * ‖r + 1‖ * ‖y‖ ^ 2 := by ring
    _ = |(r - 1) * (r + 1) * ‖y‖ ^ 2| := by simp [abs_mul]
    _ = |r ^ 2 * ‖y‖ ^ 2 - ‖y‖ ^ 2| := by ring_nf
    _ = |‖x‖ ^ 2 - ‖y‖ ^ 2| := by simp [hxy, norm_smul, mul_pow, sq_abs]
    _ = |‖z + y‖ ^ 2 - ‖z - x‖ ^ 2| := by
      simp [norm_add_sq_real, norm_sub_sq_real, hzy, hzx, abs_sub_comm]
#align inner_product_geometry.mul_norm_eq_abs_sub_sq_norm InnerProductGeometry.mul_norm_eq_abs_sub_sq_norm

end InnerProductGeometry

namespace EuclideanGeometry

/-!
### Geometrical results on spheres in Euclidean affine spaces

This section develops some results on spheres in Euclidean affine spaces.
-/


open InnerProductGeometry

variable {P : Type*} [MetricSpace P] [NormedAddTorsor V P]

/-- If `P` is a point on the line `AB` and `Q` is equidistant from `A` and `B`, then
`AP * BP = abs (BQ ^ 2 - PQ ^ 2)`. -/
theorem mul_dist_eq_abs_sub_sq_dist {a b p q : P} (hp : ∃ k : ℝ, k ≠ 1 ∧ b -ᵥ p = k • (a -ᵥ p))
    (hq : dist a q = dist b q) : dist a p * dist b p = |dist b q ^ 2 - dist p q ^ 2| := by
  let m : P := midpoint ℝ a b
  have h1 := vsub_sub_vsub_cancel_left a p m
  have h2 := vsub_sub_vsub_cancel_left p q m
  have h3 := vsub_sub_vsub_cancel_left a q m
  have h : ∀ r, b -ᵥ r = m -ᵥ r + (m -ᵥ a) := fun r => by
    rw [midpoint_vsub_left, ← right_vsub_midpoint, add_comm, vsub_add_vsub_cancel]
  iterate 4 rw [dist_eq_norm_vsub V]
  rw [← h1, ← h2, h, h]
  rw [← h1, h] at hp
  rw [dist_eq_norm_vsub V a q, dist_eq_norm_vsub V b q, ← h3, h] at hq
  exact mul_norm_eq_abs_sub_sq_norm hp hq
#align euclidean_geometry.mul_dist_eq_abs_sub_sq_dist EuclideanGeometry.mul_dist_eq_abs_sub_sq_dist

/-- If `A`, `B`, `C`, `D` are cospherical and `P` is on both lines `AB` and `CD`, then
`AP * BP = CP * DP`. -/
theorem mul_dist_eq_mul_dist_of_cospherical {a b c d p : P} (h : Cospherical ({a, b, c, d} : Set P))
    (hapb : ∃ k₁ : ℝ, k₁ ≠ 1 ∧ b -ᵥ p = k₁ • (a -ᵥ p))
    (hcpd : ∃ k₂ : ℝ, k₂ ≠ 1 ∧ d -ᵥ p = k₂ • (c -ᵥ p)) :
    dist a p * dist b p = dist c p * dist d p := by
  obtain ⟨q, r, h'⟩ := (cospherical_def {a, b, c, d}).mp h
  obtain ⟨ha, hb, hc, hd⟩ := h' a (by simp), h' b (by simp), h' c (by simp), h' d (by simp)
  rw [← hd] at hc
  rw [← hb] at ha
  rw [mul_dist_eq_abs_sub_sq_dist hapb ha, hb, mul_dist_eq_abs_sub_sq_dist hcpd hc, hd]
#align euclidean_geometry.mul_dist_eq_mul_dist_of_cospherical EuclideanGeometry.mul_dist_eq_mul_dist_of_cospherical

/-- **Intersecting Chords Theorem**. -/
theorem mul_dist_eq_mul_dist_of_cospherical_of_angle_eq_pi {a b c d p : P}
    (h : Cospherical ({a, b, c, d} : Set P)) (hapb : ∠ a p b = π) (hcpd : ∠ c p d = π) :
    dist a p * dist b p = dist c p * dist d p := by
  obtain ⟨-, k₁, _, hab⟩ := angle_eq_pi_iff.mp hapb
  obtain ⟨-, k₂, _, hcd⟩ := angle_eq_pi_iff.mp hcpd
  exact mul_dist_eq_mul_dist_of_cospherical h ⟨k₁, by linarith, hab⟩ ⟨k₂, by linarith, hcd⟩
#align euclidean_geometry.mul_dist_eq_mul_dist_of_cospherical_of_angle_eq_pi EuclideanGeometry.mul_dist_eq_mul_dist_of_cospherical_of_angle_eq_pi

/-- **Intersecting Secants Theorem**. -/
theorem mul_dist_eq_mul_dist_of_cospherical_of_angle_eq_zero {a b c d p : P}
    (h : Cospherical ({a, b, c, d} : Set P)) (hab : a ≠ b) (hcd : c ≠ d) (hapb : ∠ a p b = 0)
    (hcpd : ∠ c p d = 0) : dist a p * dist b p = dist c p * dist d p := by
  obtain ⟨-, k₁, -, hab₁⟩ := angle_eq_zero_iff.mp hapb
  obtain ⟨-, k₂, -, hcd₁⟩ := angle_eq_zero_iff.mp hcpd
  refine mul_dist_eq_mul_dist_of_cospherical h ⟨k₁, ?_, hab₁⟩ ⟨k₂, ?_, hcd₁⟩ <;> by_contra hnot <;>
    simp_all only [Classical.not_not, one_smul]
  exacts [hab (vsub_left_cancel hab₁).symm, hcd (vsub_left_cancel hcd₁).symm]
#align euclidean_geometry.mul_dist_eq_mul_dist_of_cospherical_of_angle_eq_zero EuclideanGeometry.mul_dist_eq_mul_dist_of_cospherical_of_angle_eq_zero

end EuclideanGeometry
