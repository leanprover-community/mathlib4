/-
Copyright (c) 2021 Manuel Candales. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Candales, Benjamin Davidson, Li Jiale
-/
module

public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
public import Mathlib.Geometry.Euclidean.Sphere.Tangent
public import Mathlib.Geometry.Euclidean.Circumcenter

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
* `Sphere.inner_vsub_vsub_eq_power`: The signed power of a point, `⟪a -ᵥ p, b -ᵥ p⟫`, equals the
  power of `p`; this unifies the chord and secant cases without splitting on the sign.
* `Sphere.dist_sq_eq_mul_dist_of_tangent_and_secant`: Tangent-Secant Theorem.
* `cospherical_of_inner_vsub_eq_inner_vsub`: A dimension-free converse to power of a point, stated
  with the signed invariant.
* `cospherical_of_mul_dist_eq_mul_dist_of_angle_eq_pi`: Converse of the Intersecting Chords Theorem.
* `cospherical_of_mul_dist_eq_mul_dist_of_angle_eq_zero`: Converse of the Intersecting Secants
  Theorem.
-/

@[expose] public section


open Real EuclideanGeometry RealInnerProductSpace

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


open InnerProductGeometry

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

/-- Signed power of a point on a secant line: if `a` and `b` lie on `s` and `p` lies on the
line `ab`, then `⟪a -ᵥ p, b -ᵥ p⟫` is exactly the power of `p` with respect to `s`. -/
theorem inner_vsub_vsub_eq_power {s : Sphere P} {a b p : P}
    (ha : a ∈ s) (hb : b ∈ s) (hp : p ∈ line[ℝ, a, b]) :
    ⟪a -ᵥ p, b -ᵥ p⟫ = s.power p := by
  obtain ⟨t, rfl⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hp
  set A : V := a -ᵥ s.center with hA
  set B : V := b -ᵥ s.center with hB
  have ha' : ⟪A, A⟫ = s.radius ^ 2 := by
    rw [hA, real_inner_self_eq_norm_sq, ← dist_eq_norm_vsub V, mem_sphere.mp ha]
  have hb' : ⟪B, B⟫ = s.radius ^ 2 := by
    rw [hB, real_inner_self_eq_norm_sq, ← dist_eq_norm_vsub V, mem_sphere.mp hb]
  have hap : (a -ᵥ AffineMap.lineMap a b t : V) = t • (A - B) := by
    rw [AffineMap.left_vsub_lineMap, hA, hB, vsub_sub_vsub_cancel_right]
  have hbp : (b -ᵥ AffineMap.lineMap a b t : V) = (1 - t) • (B - A) := by
    rw [AffineMap.right_vsub_lineMap, hA, hB, vsub_sub_vsub_cancel_right]
  have hpc : (AffineMap.lineMap a b t -ᵥ s.center : V) = A + t • (B - A) := by
    rw [← vsub_add_vsub_cancel (AffineMap.lineMap a b t) a s.center,
      AffineMap.lineMap_vsub_left, hA, hB, vsub_sub_vsub_cancel_right, add_comm]
  rw [Sphere.power, dist_eq_norm_vsub V, ← real_inner_self_eq_norm_sq, hap, hbp, hpc]
  simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right]
  linear_combination (t - 1) * ha' - t * hb'

/-- A one-secant converse to signed power.  If `a ∈ s`, `x` lies on the line `pa`, and the
signed product `⟪a -ᵥ p, x -ᵥ p⟫` equals the power of `p`, then `x ∈ s`. -/
theorem mem_of_inner_vsub_vsub_eq_power_of_mem_line {s : Sphere P} {a p x : P}
    (ha : a ∈ s) (hx : x ∈ line[ℝ, p, a])
    (hpow : ⟪a -ᵥ p, x -ᵥ p⟫ = s.power p) :
    x ∈ s := by
  obtain ⟨t, rfl⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hx
  set A : V := a -ᵥ s.center with hA
  set y : V := p -ᵥ s.center with hy
  have ha' : ⟪A, A⟫ = s.radius ^ 2 := by
    rw [hA, real_inner_self_eq_norm_sq, ← dist_eq_norm_vsub V, mem_sphere.mp ha]
  have hap : (a -ᵥ p : V) = A - y := by rw [hA, hy, vsub_sub_vsub_cancel_right]
  have hxp : (AffineMap.lineMap p a t -ᵥ p : V) = t • (A - y) := by
    rw [AffineMap.lineMap_vsub_left, hap]
  have hxc : (AffineMap.lineMap p a t -ᵥ s.center : V) = y + t • (A - y) := by
    rw [← vsub_add_vsub_cancel (AffineMap.lineMap p a t) p s.center, hxp, ← hy]; abel
  rw [hap, hxp, Sphere.power, dist_eq_norm_vsub V, ← real_inner_self_eq_norm_sq, ← hy] at hpow
  rw [mem_sphere, dist_eq_norm_vsub V,
    ← pow_left_inj₀ (norm_nonneg _) (radius_nonneg_of_mem ha) two_ne_zero,
    ← real_inner_self_eq_norm_sq, hxc]
  simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right] at hpow ⊢
  linear_combination t * ha' + (t - 1) * hpow

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
    rw [mem_orthRadius_iff_inner_left]
    obtain ⟨r, hr⟩ := (vadd_right_mem_affineSpan_pair (k := ℝ)).mp (vsub_vadd x t ▸ hx)
    rw [← hr, inner_smul_left, h_orth, mul_zero]⟩

alias ⟨_, isTangentAt_of_dist_sq_eq_power⟩ := isTangentAt_iff_dist_sq_eq_power

end Sphere

/-! ### Converse direction: equal products imply cospherical -/

/-- A dimension-free converse to power of a point in signed form.  If `p` lies on both lines
`p₁p₂` and `p₃p₄`, and the two signed power products are equal, then the four endpoints are
cospherical. -/
theorem cospherical_of_inner_vsub_eq_inner_vsub {p₁ p₂ p₃ p₄ p : P}
    (h₁₂ : p ∈ line[ℝ, p₁, p₂]) (h₃₄ : p ∈ line[ℝ, p₃, p₄])
    (hn : ¬ Collinear ℝ ({p₁, p, p₃} : Set P))
    (hpow : ⟪p₁ -ᵥ p, p₂ -ᵥ p⟫ = ⟪p₃ -ᵥ p, p₄ -ᵥ p⟫) :
    Cospherical ({p₁, p₂, p₃, p₄} : Set P) := by
  have hpp₃ : p ≠ p₃ := by
    rintro rfl; exact hn (by simpa using collinear_pair ℝ p₁ p)
  have hp₁p₃ : p₁ ≠ p₃ := by
    rintro rfl; exact hn (by simpa using collinear_pair ℝ p p₁)
  have hp₁p₂ : p₁ ≠ p₂ := by
    rintro rfl
    have hpeq : p = p₁ := by simpa using h₁₂
    exact hn (by rw [hpeq]; simpa using collinear_pair ℝ p₁ p₃)
  have hn₁₂₃ : ¬ Collinear ℝ ({p₁, p₂, p₃} : Set P) := by
    intro hcol
    apply hn
    have hp₂_mem : p₂ ∈ line[ℝ, p₁, p₃] :=
      hcol.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hp₁p₃
    have hp_mem : p ∈ line[ℝ, p₁, p₃] := by
      rwa [affineSpan_pair_eq_of_right_mem_of_ne hp₂_mem hp₁p₂.symm] at h₁₂
    simpa [Set.insert_comm] using collinear_insert_of_mem_affineSpan_pair hp_mem
  let t : Affine.Triangle ℝ P :=
    ⟨![p₁, p₂, p₃], affineIndependent_iff_not_collinear_set.mpr hn₁₂₃⟩
  have hp₁_mem : p₁ ∈ t.circumsphere := t.mem_circumsphere 0
  have hp₂_mem : p₂ ∈ t.circumsphere := t.mem_circumsphere 1
  have hp₃_mem : p₃ ∈ t.circumsphere := t.mem_circumsphere 2
  have hleft : ⟪p₁ -ᵥ p, p₂ -ᵥ p⟫ = t.circumsphere.power p :=
    Sphere.inner_vsub_vsub_eq_power hp₁_mem hp₂_mem h₁₂
  have hp₄_line : p₄ ∈ line[ℝ, p, p₃] :=
    (collinear_insert_of_mem_affineSpan_pair h₃₄).mem_affineSpan_of_mem_of_ne
      (by simp) (by simp) (by simp) hpp₃
  have hp₄_mem : p₄ ∈ t.circumsphere :=
    Sphere.mem_of_inner_vsub_vsub_eq_power_of_mem_line hp₃_mem hp₄_line
      (hpow.symm.trans hleft)
  rw [cospherical_iff_exists_sphere]
  refine ⟨t.circumsphere, ?_⟩
  simp only [Set.insert_subset_iff, Set.singleton_subset_iff]
  exact ⟨hp₁_mem, hp₂_mem, hp₃_mem, hp₄_mem⟩

/-- **Converse of the Intersecting Chords Theorem**. If `p` lies between `p₁` and `p₂` and
between `p₃` and `p₄`, and `dist p₁ p * dist p₂ p = dist p₃ p * dist p₄ p`, then the four
points are cospherical. -/
theorem cospherical_of_mul_dist_eq_mul_dist_of_angle_eq_pi {p₁ p₂ p₃ p₄ p : P}
    (h : dist p₁ p * dist p₂ p = dist p₃ p * dist p₄ p)
    (hp₁p₂ : ∠ p₁ p p₂ = π) (hp₃p₄ : ∠ p₃ p p₄ = π)
    (hn : ¬ Collinear ℝ ({p₁, p, p₃} : Set P)) :
    Cospherical ({p₁, p₂, p₃, p₄} : Set P) := by
  refine cospherical_of_inner_vsub_eq_inner_vsub
    (angle_eq_pi_iff_sbtw.mp hp₁p₂).wbtw.mem_affineSpan
    (angle_eq_pi_iff_sbtw.mp hp₃p₄).wbtw.mem_affineSpan hn ?_
  rw [← cos_angle_mul_dist_mul_dist, ← cos_angle_mul_dist_mul_dist, hp₁p₂, hp₃p₄, h]

/-- **Converse of the Intersecting Secants Theorem**. If `p₁` and `p₂` lie on one ray from
`p` and `p₃` and `p₄` on another, and `dist p₁ p * dist p₂ p = dist p₃ p * dist p₄ p`, then
the four points are cospherical. The hypotheses `p₁ ≠ p₂` and `p₃ ≠ p₄` are needed because
`∠ p₁ p p₂ = 0` does not force the endpoints to be distinct. -/
theorem cospherical_of_mul_dist_eq_mul_dist_of_angle_eq_zero {p₁ p₂ p₃ p₄ p : P}
    (h : dist p₁ p * dist p₂ p = dist p₃ p * dist p₄ p)
    (h₁₂ : p₁ ≠ p₂) (h₃₄ : p₃ ≠ p₄)
    (hp₁p₂ : ∠ p₁ p p₂ = 0) (hp₃p₄ : ∠ p₃ p p₄ = 0)
    (hn : ¬ Collinear ℝ ({p₁, p, p₃} : Set P)) :
    Cospherical ({p₁, p₂, p₃, p₄} : Set P) := by
  refine cospherical_of_inner_vsub_eq_inner_vsub
    ((collinear_of_angle_eq_zero hp₁p₂).mem_affineSpan_of_mem_of_ne
      (by simp) (by simp) (by simp) h₁₂)
    ((collinear_of_angle_eq_zero hp₃p₄).mem_affineSpan_of_mem_of_ne
      (by simp) (by simp) (by simp) h₃₄) hn ?_
  rw [← cos_angle_mul_dist_mul_dist, ← cos_angle_mul_dist_mul_dist, hp₁p₂, hp₃p₄, h]

end EuclideanGeometry
