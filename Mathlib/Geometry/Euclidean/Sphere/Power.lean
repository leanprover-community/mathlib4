/-
Copyright (c) 2021 Manuel Candales. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Candales, Benjamin Davidson, Li Jiale
-/
module

public import Mathlib.Geometry.Euclidean.Angle.Sphere
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
public import Mathlib.Geometry.Euclidean.Sphere.Tangent

import Mathlib.Geometry.Euclidean.Similarity

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

@[expose] public section


open Real EuclideanGeometry RealInnerProductSpace Real Module FiniteDimensional

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

namespace InnerProductGeometry

/-!
### Geometrical results on spheres in real inner product spaces

This section develops some results on spheres in real inner product spaces,
which are used to deduce corresponding results for Euclidean affine spaces.
-/


theorem mul_norm_eq_abs_sub_sq_norm {x y z : V} (h₁ : ∃ k : ℝ, x = k • y)
    (h₃ : ‖z - y‖ = ‖z + y‖) : ‖x - y‖ * ‖x + y‖ = |‖z + y‖ ^ 2 - ‖z - x‖ ^ 2| := by
  obtain ⟨r, hr⟩ := h₁
  have hzy : ⟪z, y⟫ = 0 := by
    rwa [inner_eq_zero_iff_angle_eq_pi_div_two, ← norm_add_eq_norm_sub_iff_angle_eq_pi_div_two,
      eq_comm]
  have hzx : ⟪z, x⟫ = 0 := by rw [hr, inner_smul_right, hzy, mul_zero]
  calc
    ‖x - y‖ * ‖x + y‖ = ‖(r - 1) • y‖ * ‖(r + 1) • y‖ := by simp [sub_smul, add_smul, hr]
    _ = ‖r - 1‖ * ‖y‖ * (‖r + 1‖ * ‖y‖) := by simp_rw [norm_smul]
    _ = ‖r - 1‖ * ‖r + 1‖ * ‖y‖ ^ 2 := by ring
    _ = |(r - 1) * (r + 1) * ‖y‖ ^ 2| := by simp [abs_mul]
    _ = |r ^ 2 * ‖y‖ ^ 2 - ‖y‖ ^ 2| := by ring_nf
    _ = |‖x‖ ^ 2 - ‖y‖ ^ 2| := by simp [hr, norm_smul, mul_pow, sq_abs]
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
theorem mul_dist_eq_abs_sub_sq_dist {a b p q : P} (hp : p ∈ line[ℝ, a, b])
    (hq : dist a q = dist b q) : dist a p * dist b p = |dist b q ^ 2 - dist p q ^ 2| := by
  let m : P := midpoint ℝ a b
  have h1 := vsub_sub_vsub_cancel_left a p m
  have h1' := vsub_sub_vsub_cancel_left p a m
  have h2 := vsub_sub_vsub_cancel_left p q m
  have h3 := vsub_sub_vsub_cancel_left a q m
  have h : ∀ r, b -ᵥ r = m -ᵥ r + (m -ᵥ a) := fun r => by
    rw [midpoint_vsub_left, ← right_vsub_midpoint, add_comm, vsub_add_vsub_cancel]
  iterate 4 rw [dist_eq_norm_vsub V]
  rw [← h1, ← h2, h, h]
  rw [dist_eq_norm_vsub V a q, dist_eq_norm_vsub V b q, ← h3, h] at hq
  refine mul_norm_eq_abs_sub_sq_norm ?_ hq
  -- TODO: factor this out as a separate lemma?
  · rw [← vsub_vadd p a, vadd_left_mem_affineSpan_pair] at hp
    rcases hp with ⟨r, hr⟩
    rw [h, ← h1', eq_sub_iff_add_eq, ← eq_sub_iff_add_eq'] at hr
    rw [hr]
    use 1 - r * 2
    match_scalars
    ring

/-- If `A`, `B`, `C`, `D` are cospherical and `P` is on both lines `AB` and `CD`, then
`AP * BP = CP * DP`. -/
theorem mul_dist_eq_mul_dist_of_cospherical {a b c d p : P} (h : Cospherical ({a, b, c, d} : Set P))
    (hapb : p ∈ line[ℝ, a, b]) (hcpd : p ∈ line[ℝ, c, d]) :
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
  rw [EuclideanGeometry.angle_eq_pi_iff_sbtw] at hapb hcpd
  exact mul_dist_eq_mul_dist_of_cospherical h hapb.wbtw.mem_affineSpan hcpd.wbtw.mem_affineSpan

/-- If `p` lies strictly between `p₁` and `p₂` on one line and strictly between `p₃` and `p₄`
on another line, and if `dist p₁ p * dist p₂ p = dist p₃ p * dist p₄ p`,
then the points `p₁`, `p₂`, `p₃`, and `p₄` are cospherical. -/
theorem cospherical_of_mul_dist_eq_mul_dist_of_angle_eq_pi {p₁ p₂ p₃ p₄ p : P}
    (h : dist p₁ p * dist p₂ p = dist p₃ p * dist p₄ p)
    (hp₁p₂ : ∠ p₁ p p₂ = π) (hp₃p₄ : ∠ p₃ p p₄ = π) (hn : ¬ Collinear ℝ ({p₁, p, p₃} : Set P)) :
    Cospherical ({p₁, p₂, p₃, p₄} : Set P) := by
  suffices h_equiv : Cospherical ({p₁, p₂, p₄, p₃} : Set P) by
    grind [Set.pair_comm p₄ p₃]
  have h_angle_eq : ∠ p₁ p p₄ = ∠ p₃ p p₂ := by
    grind [angle_comm, angle_eq_angle_of_angle_eq_pi_of_angle_eq_pi hp₃p₄]
  have hp₁p₂_sbtw : Sbtw ℝ p₁ p p₂ := angle_eq_pi_iff_sbtw.mp hp₁p₂
  have hp₃p₄_sbtw : Sbtw ℝ p₃ p p₄ := angle_eq_pi_iff_sbtw.mp hp₃p₄
  have h_notcol_p₁p₂p₃ : ¬ Collinear ℝ ({p₁, p₂, p₃} : Set P) := by
    intro hcol
    have hcol_p₁pp₂ := hp₁p₂_sbtw.wbtw.collinear
    suffices hcol : Collinear ℝ ({p₁, p, p₃} : Set P) by grind
    suffices hcol_all : Collinear ℝ ({p₃, p, p₁, p₂} : Set P) by grind [Collinear.subset _ hcol_all]
    apply collinear_insert_insert_of_mem_affineSpan_pair
    · grind [Collinear.mem_affineSpan_of_mem_of_ne, hp₁p₂_sbtw.left_ne_right]
    · grind [Collinear.mem_affineSpan_of_mem_of_ne, hp₁p₂_sbtw.left_ne_right]
  have hindep : AffineIndependent ℝ ![p₁, p, p₃] := affineIndependent_iff_not_collinear_set.mpr hn
  set t : Affine.Triangle ℝ P := ⟨_, hindep⟩ with ht
  set S : AffineSubspace ℝ P := affineSpan ℝ (Set.range t.points) with hS
  have hf2 : Fact (finrank ℝ S.direction = 2) := ⟨by
    rw [hS, direction_affineSpan, t.independent.finrank_vectorSpan]
    simp⟩
  have hp₁ : p₁ ∈ S := by apply mem_affineSpan; simp [ht]
  have hp : p ∈ S := by apply mem_affineSpan; simp [ht]
  have hp₃ : p₃ ∈ S := by apply mem_affineSpan; simp [ht]
  have hp₂ : p₂ ∈ S := by
    have h1 : ({p₁, p}: Set P) ⊆ Set.range t.points := by simp [ht]; grind
    have h2 : p₂ ∈ affineSpan ℝ ({p₁, p}: Set P) := by
      simp [hp₁p₂_sbtw.wbtw.collinear.mem_affineSpan_of_mem_of_ne _ _ _ hp₁p₂_sbtw.left_ne]
    exact affineSpan_mono ℝ h1 h2
  have hp₄ : p₄ ∈ S := by
    have h1 : ({p₃, p}: Set P) ⊆ Set.range t.points := by simp [ht]; grind
    have h2 : p₄ ∈ affineSpan ℝ ({p₃, p}: Set P) := by
      simp [hp₃p₄_sbtw.wbtw.collinear.mem_affineSpan_of_mem_of_ne _ _ _ hp₃p₄_sbtw.left_ne]
    exact affineSpan_mono ℝ h1 h2
  let s_isom : AffineIsometry ℝ S P := S.subtypeₐᵢ
  let p₁' : S := ⟨p₁, hp₁⟩
  let p₂' : S := ⟨p₂, hp₂⟩
  let p₃' : S := ⟨p₃, hp₃⟩
  let p₄' : S := ⟨p₄, hp₄⟩
  let p' : S := ⟨p, hp⟩
  have h_dist : dist p₁' p' * dist p₂' p' = dist p₃' p' * dist p₄' p' := by
    simpa [dist_eq_norm_vsub, ← s_isom.dist_map] using h
  have hp₁p₂' : ∠ p₁' p' p₂' = π := by simpa [AffineIsometry.angle_map s_isom]
  have hp₃p₄' : ∠ p₃' p' p₄' = π := by simpa [AffineIsometry.angle_map s_isom]
  suffices h_cospherical' : Cospherical {p₁', p₂', p₄', p₃'} by
    have h_cosp_top := h_cospherical'.restrict le_top
    convert (⊤ : AffineSubspace ℝ P).subtypeₐᵢ.isometry.cospherical h_cosp_top
    simp [Set.image_insert_eq, Set.image_singleton]
    grind
  have h_indep_p₁p₂p₃ : AffineIndependent ℝ ![p₁, p₂, p₃] :=
    affineIndependent_iff_not_collinear_set.mpr h_notcol_p₁p₂p₃
  have h_ncol_p₁p₂p₃' : ¬ Collinear ℝ {p₁', p₂', p₃'} := by
    rw [← affineIndependent_iff_not_collinear_set,
      ← s_isom.toAffineMap.affineIndependent_iff s_isom.injective]
    convert h_indep_p₁p₂p₃
    ext i; fin_cases i <;> rfl
  have h_ncol_p₁pp₃' : ¬ Collinear ℝ {p₁', p', p₃'} := by
    rw [← affineIndependent_iff_not_collinear_set,
      ← s_isom.toAffineMap.affineIndependent_iff s_isom.injective]
    convert hindep
    ext i; fin_cases i <;> rfl
  have hf2 : Fact (finrank ℝ S.direction = 2) := ⟨by
    rw [hS, direction_affineSpan, t.independent.finrank_vectorSpan]
    simp⟩
  letI : Module.Oriented ℝ S.direction (Fin 2) :=
    ⟨Basis.orientation (finBasisOfFinrankEq _ _ hf2.out)⟩
  apply EuclideanGeometry.cospherical_of_two_zsmul_oangle_eq_of_not_collinear ?_ h_ncol_p₁p₂p₃'
  rw [EuclideanGeometry.angle_eq_pi_iff_sbtw] at hp₁p₂' hp₃p₄'
  suffices ∡ p₁' p₂' p₃' = ∡ p₁' p₄' p₃' by grind
  suffices ∠ p₁' p₂' p₃' = ∠ p₁' p₄' p₃' by
    grind [oangle_eq_of_angle_eq_of_sign_eq, Sbtw.oangle_sign_eq_of_sbtw]
  rw [angle_comm, ← angle_eq_angle_of_angle_eq_pi p₃' hp₁p₂'.angle₃₂₁_eq_pi,
    ← angle_eq_angle_of_angle_eq_pi p₁' hp₃p₄'.angle₃₂₁_eq_pi]
  suffices h_sim : Similar ![p₁', p', p₄'] ![p₃', p', p₂'] by
    grind [angle_comm, h_sim.angle_eq_all.right.left]
  have h_ncol_p₁pp₄' : ¬ Collinear ℝ {p₁', p', p₄'} := by
    intro hcol
    have hcol_p₃pp₄' := hp₃p₄'.wbtw.collinear
    suffices hcol : Collinear ℝ {p₁', p₃', p', p₄'} by
      have : Collinear ℝ {p₁', p', p₃'} := by grind [Collinear.subset _ hcol]
      exact h_ncol_p₁pp₃' this
    apply collinear_insert_insert_of_mem_affineSpan_pair
    · grind [Collinear.mem_affineSpan_of_mem_of_ne, hp₃p₄'.ne_right]
    · grind [Collinear.mem_affineSpan_of_mem_of_ne, hp₃p₄'.ne_right]
  have h_notcol_p₃pp₂' : ¬ Collinear ℝ {p₃', p', p₂'} := by
    intro hcol
    have hcol_p₁pp₂' := hp₁p₂'.wbtw.collinear
    suffices hcol : Collinear ℝ {p₃', p₁', p', p₂'} by
      have : Collinear ℝ {p₁', p', p₃'} := by grind [Collinear.subset _ hcol]
      exact h_ncol_p₁pp₃' this
    apply collinear_insert_insert_of_mem_affineSpan_pair
    · grind [Collinear.mem_affineSpan_of_mem_of_ne, hp₁p₂'.ne_right]
    · grind [Collinear.mem_affineSpan_of_mem_of_ne, hp₁p₂'.ne_right]
  have h_angle' : ∠ p₁' p' p₄' = ∠ p₃' p' p₂' := by simpa [AffineIsometry.angle_map s_isom]
  exact similar_of_side_angle_side h_ncol_p₁pp₄' h_notcol_p₃pp₂' h_angle' (by grind [dist_comm])

/-- **Intersecting Secants Theorem**. -/
theorem mul_dist_eq_mul_dist_of_cospherical_of_angle_eq_zero {a b c d p : P}
    (h : Cospherical ({a, b, c, d} : Set P)) (hab : a ≠ b) (hcd : c ≠ d) (hapb : ∠ a p b = 0)
    (hcpd : ∠ c p d = 0) : dist a p * dist b p = dist c p * dist d p := by
  apply collinear_of_angle_eq_zero at hapb
  apply collinear_of_angle_eq_zero at hcpd
  exact mul_dist_eq_mul_dist_of_cospherical h
    (hapb.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hab)
    (hcpd.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hcd)

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
    (hp : p ∈ line[ℝ, a, b])
    (ha : a ∈ s) (hb : b ∈ s) :
    dist p a * dist p b = |s.power p| := by
  have hq : dist a s.center = dist b s.center := by
    rw [mem_sphere.mp ha, mem_sphere.mp hb]
  rw [dist_comm p a, dist_comm p b, mul_dist_eq_abs_sub_sq_dist hp hq,
    mem_sphere.mp hb, power, abs_sub_comm]

/-- For a point on the sphere, the product of distances to two other intersection
points on a line through the point is zero. -/
theorem mul_dist_eq_zero_of_mem_sphere {s : Sphere P} {p a b : P}
    (hp : p ∈ line[ℝ, a, b])
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
    (hp : p ∈ line[ℝ, a, b])
    (ha : a ∈ s) (hb : b ∈ s)
    (hle : s.radius ≤ dist p s.center) :
    dist p a * dist p b = s.power p := by
  rw [mul_dist_eq_abs_power hp ha hb,
    abs_of_nonneg <| (power_nonneg_iff_radius_le_dist_center hr).mpr hle]

/-- For a point inside or on the sphere, the product of distances to two intersection
points on a line through the point equals the negative of the power of the point. -/
theorem mul_dist_eq_neg_power_of_dist_center_le_radius {s : Sphere P} {p a b : P}
    (hr : 0 ≤ s.radius)
    (hp : p ∈ line[ℝ, a, b])
    (ha : a ∈ s) (hb : b ∈ s)
    (hle : dist p s.center ≤ s.radius) :
    dist p a * dist p b = -s.power p := by
  rw [mul_dist_eq_abs_power hp ha hb,
    abs_of_nonpos <| (power_nonpos_iff_dist_center_le_radius hr).mpr hle]

/-- **Tangent-Secant Theorem**. The square of the tangent length equals
    the product of secant segment lengths. -/
theorem dist_sq_eq_mul_dist_of_tangent_and_secant {a b t p : P} {s : Sphere P}
    (ha : a ∈ s) (hb : b ∈ s)
    (hp : p ∈ line[ℝ, a, b])
    (h_tangent : s.IsTangentAt t (line[ℝ, p, t])) :
    dist p t ^ 2 = dist p a * dist p b := by
  have hr := radius_nonneg_of_mem ha
  have radius_le_dist := h_tangent.isTangent.radius_le_dist_center (left_mem_affineSpan_pair ℝ p t)
  rw [mul_dist_eq_power_of_radius_le_dist_center hr hp ha hb radius_le_dist,
    Sphere.power, h_tangent.dist_sq_eq_of_mem (left_mem_affineSpan_pair ℝ p t)]
  ring

/-- The power of a point with respect to a sphere equals the square of its tangent length. -/
theorem IsTangentAt.power_eq_dist_sq {s : Sphere P} {t p : P}
    (h_tangent : s.IsTangentAt t (line[ℝ, p, t])) :
    s.power p = dist p t ^ 2 := by
  rw [Sphere.power, h_tangent.dist_sq_eq_of_mem (left_mem_affineSpan_pair ℝ p t)]
  ring_nf

/-- A line through a point on a sphere is tangent if and only if the squared distance
from the external point to the tangent point equals the power of the point. -/
theorem isTangentAt_iff_dist_sq_eq_power {t p : P} {s : Sphere P} (ht : t ∈ s) :
    s.IsTangentAt t (line[ℝ, p, t]) ↔ dist p t ^ 2 = s.power p :=
  ⟨fun h ↦ h.power_eq_dist_sq.symm, fun h_dist_eq ↦ by
    have h_orth : ⟪p -ᵥ t, t -ᵥ s.center⟫ = 0 := by
      simp only [Sphere.power, ← mem_sphere.mp ht, dist_eq_norm_vsub V, sq,
                 ← vsub_add_vsub_cancel p t s.center] at h_dist_eq
      exact (norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero _ _).mp (by linarith)
    refine ⟨ht, right_mem_affineSpan_pair ℝ p t, fun x hx ↦ ?_⟩
    rw [SetLike.mem_coe, mem_orthRadius_iff_inner_left]
    obtain ⟨r, hr⟩ := (vadd_right_mem_affineSpan_pair (k := ℝ)).mp (vsub_vadd x t ▸ hx)
    rw [← hr, inner_smul_left, h_orth, mul_zero]⟩

alias ⟨_, isTangentAt_of_dist_sq_eq_power⟩ := isTangentAt_iff_dist_sq_eq_power

end Sphere

end EuclideanGeometry
