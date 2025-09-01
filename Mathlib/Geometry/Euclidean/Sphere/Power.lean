/-
Copyright (c) 2021 Manuel Candales. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Candales, Benjamin Davidson
-/
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
import Mathlib.Geometry.Euclidean.Sphere.Basic
import Mathlib.Geometry.Euclidean.Sphere.Tangent

/-!
# Power of a point (intersecting chords and secants)

This file proves basic geometrical results about power of a point (intersecting chords and
secants) in spheres in real inner product spaces and Euclidean affine spaces.

## Main definitions

* `Sphere.power`: The power of a point with respect to a sphere.

## Main theorems

* `mul_dist_eq_mul_dist_of_cospherical_of_angle_eq_pi`: Intersecting Chords Theorem (Freek No. 55).
* `mul_dist_eq_mul_dist_of_cospherical_of_angle_eq_zero`: Intersecting Secants Theorem.
* `Sphere.mul_dist_eq_abs_power`: The product of distances equals the absolute value of power.
* `Sphere.dist_sq_eq_mul_dist_of_tangent_and_secant`: Tangent-Secant Theorem.
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

end InnerProductGeometry

namespace EuclideanGeometry

/-!
### Geometrical results on spheres in Euclidean affine spaces

This section develops some results on spheres in Euclidean affine spaces.
-/


open InnerProductGeometry EuclideanGeometry

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

/-- **Intersecting Chords Theorem**. -/
theorem mul_dist_eq_mul_dist_of_cospherical_of_angle_eq_pi {a b c d p : P}
    (h : Cospherical ({a, b, c, d} : Set P)) (hapb : ∠ a p b = π) (hcpd : ∠ c p d = π) :
    dist a p * dist b p = dist c p * dist d p := by
  obtain ⟨-, k₁, _, hab⟩ := angle_eq_pi_iff.mp hapb
  obtain ⟨-, k₂, _, hcd⟩ := angle_eq_pi_iff.mp hcpd
  exact mul_dist_eq_mul_dist_of_cospherical h ⟨k₁, by linarith, hab⟩ ⟨k₂, by linarith, hcd⟩

/-- **Intersecting Secants Theorem**. -/
theorem mul_dist_eq_mul_dist_of_cospherical_of_angle_eq_zero {a b c d p : P}
    (h : Cospherical ({a, b, c, d} : Set P)) (hab : a ≠ b) (hcd : c ≠ d) (hapb : ∠ a p b = 0)
    (hcpd : ∠ c p d = 0) : dist a p * dist b p = dist c p * dist d p := by
  obtain ⟨-, k₁, -, hab₁⟩ := angle_eq_zero_iff.mp hapb
  obtain ⟨-, k₂, -, hcd₁⟩ := angle_eq_zero_iff.mp hcpd
  refine mul_dist_eq_mul_dist_of_cospherical h ⟨k₁, ?_, hab₁⟩ ⟨k₂, ?_, hcd₁⟩ <;> by_contra hnot <;>
    simp_all only [one_smul]
  exacts [hab (vsub_left_cancel hab₁).symm, hcd (vsub_left_cancel hcd₁).symm]

namespace Sphere

/-- The power of a point with respect to a sphere. For a point and a sphere,
this is defined as the square of the distance from the point to the center
minus the square of the radius. This value is positive if the point is outside
the sphere, negative if inside, and zero if on the sphere. -/
def power (s : Sphere P) (p : P) : ℝ :=
  dist p s.center ^ 2 - s.radius ^ 2

/-- A point lies on the sphere if and only if its power with respect to
the sphere is zero. -/
theorem power_eq_zero_iff_mem_sphere {s : Sphere P} {p : P} (hr : 0 ≤ s.radius) :
    s.power p = 0 ↔ p ∈ s := by
  rw [power, mem_sphere, sub_eq_zero, pow_left_inj₀ dist_nonneg hr two_ne_zero]

/-- The power of a point is positive if and only if the point lies outside the sphere. -/
theorem power_pos_iff_radius_lt_dist_center {s : Sphere P} {p : P} (hr : 0 ≤ s.radius) :
    0 < s.power p ↔ s.radius < dist p s.center := by
  rw [power, sub_pos, pow_lt_pow_iff_left₀ hr dist_nonneg two_ne_zero]

/-- The power of a point is negative if and only if the point lies inside the sphere. -/
theorem power_neg_iff_dist_center_lt_radius {s : Sphere P} {p : P} (hr : 0 ≤ s.radius) :
  s.power p < 0 ↔ dist p s.center < s.radius := by
  rw [power, sub_neg, pow_lt_pow_iff_left₀ dist_nonneg hr two_ne_zero]

/-- The power of a point is nonnegative if and only if the point lies outside or on the sphere. -/
theorem power_nonneg_iff_radius_le_dist_center {s : Sphere P} {p : P} (hr : 0 ≤ s.radius) :
    0 ≤ s.power p ↔ s.radius ≤ dist p s.center := by
  rw [power, sub_nonneg, pow_le_pow_iff_left₀ hr dist_nonneg two_ne_zero]

/-- The power of a point is nonpositive if and only if the point lies inside or on the sphere. -/
theorem power_nonpos_iff_dist_center_le_radius {s : Sphere P} {p : P} (hr : 0 ≤ s.radius) :
    s.power p ≤ 0 ↔ dist p s.center ≤ s.radius := by
  rw [power, sub_nonpos, pow_le_pow_iff_left₀ dist_nonneg hr two_ne_zero]

/-- For any point, the product of distances to two intersection
points on a line through the point equals the absolute value of the power of the point. -/
theorem mul_dist_eq_abs_power {s : Sphere P} {p a b : P}
    (hp : ∃ k : ℝ, k ≠ 1 ∧ b -ᵥ p = k • (a -ᵥ p))
    (ha : a ∈ s) (hb : b ∈ s) :
    dist p a * dist p b = |s.power p| := by
  have hq : dist a s.center = dist b s.center := by
    rw [mem_sphere.mp ha, mem_sphere.mp hb]
  rw [dist_comm p a, dist_comm p b, mul_dist_eq_abs_sub_sq_dist hp hq,
    mem_sphere.mp hb, power, abs_sub_comm]

/-- For a point on the sphere, the product of distances to two other intersection
points on a line through the point is zero. -/
theorem mul_dist_eq_zero_of_mem_sphere {s : Sphere P} {p a b : P}
    (hp : ∃ k : ℝ, k ≠ 1 ∧ b -ᵥ p = k • (a -ᵥ p))
    (ha : a ∈ s) (hb : b ∈ s)
    (hp_on : p ∈ s) :
    dist p a * dist p b = 0 := by
  have hq : dist a s.center = dist b s.center := by
    rw [mem_sphere.mp ha, mem_sphere.mp hb]
  rw [dist_comm p a, dist_comm p b, mul_dist_eq_abs_sub_sq_dist hp hq,
      mem_sphere.mp hb, mem_sphere.mp hp_on, sub_self, abs_zero]

/-- For a point outside or on the sphere, the product of distances to two intersection
points on a line through the point equals the power of the point. -/
theorem mul_dist_eq_power_of_radius_le_dist_center {s : Sphere P} {p a b : P}
    (hr : 0 ≤ s.radius)
    (hp : ∃ k : ℝ, k ≠ 1 ∧ b -ᵥ p = k • (a -ᵥ p))
    (ha : a ∈ s) (hb : b ∈ s)
    (hle : s.radius ≤ dist p s.center) :
    dist p a * dist p b = s.power p := by
  rw [mul_dist_eq_abs_power hp ha hb,
    abs_of_nonneg <| (power_nonneg_iff_radius_le_dist_center hr).mpr hle]

/-- For a point inside or on the sphere, the product of distances to two intersection
points on a line through the point equals the negative of the power of the point. -/
theorem mul_dist_eq_neg_power_of_dist_center_le_radius {s : Sphere P} {p a b : P}
    (hr : 0 ≤ s.radius)
    (hp : ∃ k : ℝ, k ≠ 1 ∧ b -ᵥ p = k • (a -ᵥ p))
    (ha : a ∈ s) (hb : b ∈ s)
    (hle : dist p s.center ≤ s.radius) :
    dist p a * dist p b = -s.power p := by
  rw [mul_dist_eq_abs_power hp ha hb,
    abs_of_nonpos <| (power_nonpos_iff_dist_center_le_radius hr).mpr hle]

/-- **Tangent-Secant Theorem**. The square of the tangent length equals
    the product of secant segment lengths. -/
theorem dist_sq_eq_mul_dist_of_tangent_and_secant {a b t p : P} {s : Sphere P}
    (ha : a ∈ s) (hb : b ∈ s)
    (h_secant : ∃ k : ℝ, k ≠ 1 ∧ b -ᵥ p = k • (a -ᵥ p))
    (h_tangent : s.IsTangentAt t (line[ℝ, p, t])) :
    dist p t ^ 2 = dist p a * dist p b := by
  have hr := radius_nonneg_of_mem ha
  have h_outside : s.radius ≤ dist p s.center := by
    rw [dist_comm]
    by_contra! hlt
    exact h_tangent.isTangent.notMem_of_dist_lt hlt (left_mem_affineSpan_pair ℝ p t)
  rw [mul_dist_eq_power_of_radius_le_dist_center hr h_secant ha hb h_outside,
    Sphere.power, h_tangent.dist_sq_eq_of_mem (left_mem_affineSpan_pair ℝ p t)]
  ring

end Sphere

end EuclideanGeometry
