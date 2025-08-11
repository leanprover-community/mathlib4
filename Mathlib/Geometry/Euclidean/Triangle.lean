/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Manuel Candales
-/
import Mathlib.Geometry.Euclidean.Angle.Oriented.Affine
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
import Mathlib.Tactic.IntervalCases

/-!
# Triangles

This file proves basic geometrical results about distances and angles
in (possibly degenerate) triangles in real inner product spaces and
Euclidean affine spaces. More specialized results, and results
developed for simplices in general rather than just for triangles, are
in separate files. Definitions and results that make sense in more
general affine spaces rather than just in the Euclidean case go under
`LinearAlgebra.AffineSpace`.

## Implementation notes

Results in this file are generally given in a form with only those
non-degeneracy conditions needed for the particular result, rather
than requiring affine independence of the points of a triangle
unnecessarily.

## References

* https://en.wikipedia.org/wiki/Law_of_cosines
* https://en.wikipedia.org/wiki/Pons_asinorum
* https://en.wikipedia.org/wiki/Sum_of_angles_of_a_triangle
* https://en.wikipedia.org/wiki/Law_of_sines

-/

noncomputable section

open scoped CharZero Real RealInnerProductSpace

namespace InnerProductGeometry

/-!
### Geometrical results on triangles in real inner product spaces

This section develops some results on (possibly degenerate) triangles
in real inner product spaces, where those definitions and results can
most conveniently be developed in terms of vectors and then used to
deduce corresponding results for Euclidean affine spaces.
-/

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- **Law of cosines** (cosine rule), vector angle form. -/
theorem norm_sub_sq_eq_norm_sq_add_norm_sq_sub_two_mul_norm_mul_norm_mul_cos_angle (x y : V) :
    ‖x - y‖ * ‖x - y‖ = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ - 2 * ‖x‖ * ‖y‖ * Real.cos (angle x y) := by
  rw [show 2 * ‖x‖ * ‖y‖ * Real.cos (angle x y) = 2 * (Real.cos (angle x y) * (‖x‖ * ‖y‖)) by ring,
    cos_angle_mul_norm_mul_norm, ← real_inner_self_eq_norm_mul_norm, ←
    real_inner_self_eq_norm_mul_norm, ← real_inner_self_eq_norm_mul_norm, real_inner_sub_sub_self,
    sub_add_eq_add_sub]

/-- **Law of sines** (sine rule), vector angle form. -/
theorem sin_angle_mul_norm_eq_sin_angle_mul_norm (x y : V) :
    Real.sin (angle x y) * ‖x‖ = Real.sin (angle y (x - y)) * ‖x - y‖ := by
  obtain rfl | hy := eq_or_ne y 0
  · norm_num
  obtain rfl | hx := eq_or_ne x 0
  · simp [angle_neg_right, angle_self hy]
  obtain rfl | hxy := eq_or_ne x y
  · simp [angle_self hx]
  have h_sin (x y : V) (hx : x ≠ 0) (hy : y ≠ 0) :
      Real.sin (angle x y) = √(⟪x, x⟫ * ⟪y, y⟫ - ⟪x, y⟫ * ⟪x, y⟫) / (‖x‖ * ‖y‖) := by
    field_simp [sin_angle_mul_norm_mul_norm]
  rw [h_sin x y hx hy, h_sin y (x - y) hy (sub_ne_zero_of_ne hxy)]
  have hsub : x - y ≠ 0 := sub_ne_zero_of_ne hxy
  field_simp [mul_assoc, inner_sub_left, inner_sub_right, real_inner_comm x y, hsub]
  ring_nf

/-- A variant of the law of sines, (two given sides are nonzero), vector angle form. -/
theorem sin_angle_div_norm_eq_sin_angle_div_norm (x y : V) (hx : x ≠ 0) (hxy : x - y ≠ 0) :
    Real.sin (angle x y) / ‖x - y‖ = Real.sin (angle y (x - y)) / ‖x‖ := by
  field_simp [sin_angle_mul_norm_eq_sin_angle_mul_norm x y]

/-- **Pons asinorum**, vector angle form. -/
theorem angle_sub_eq_angle_sub_rev_of_norm_eq {x y : V} (h : ‖x‖ = ‖y‖) :
    angle x (x - y) = angle y (y - x) := by
  refine Real.injOn_cos ⟨angle_nonneg _ _, angle_le_pi _ _⟩ ⟨angle_nonneg _ _, angle_le_pi _ _⟩ ?_
  rw [cos_angle, cos_angle, h, ← neg_sub, norm_neg, neg_sub, inner_sub_right, inner_sub_right,
    real_inner_self_eq_norm_mul_norm, real_inner_self_eq_norm_mul_norm, h, real_inner_comm x y]

/-- **Converse of pons asinorum**, vector angle form. -/
theorem norm_eq_of_angle_sub_eq_angle_sub_rev_of_angle_ne_pi {x y : V}
    (h : angle x (x - y) = angle y (y - x)) (hpi : angle x y ≠ π) : ‖x‖ = ‖y‖ := by
  replace h := Real.arccos_injOn (abs_le.mp (abs_real_inner_div_norm_mul_norm_le_one x (x - y)))
    (abs_le.mp (abs_real_inner_div_norm_mul_norm_le_one y (y - x))) h
  by_cases hxy : x = y
  · rw [hxy]
  · rw [← norm_neg (y - x), neg_sub, mul_comm, mul_comm ‖y‖, div_eq_mul_inv, div_eq_mul_inv,
      mul_inv_rev, mul_inv_rev, ← mul_assoc, ← mul_assoc] at h
    replace h :=
      mul_right_cancel₀ (inv_ne_zero fun hz => hxy (eq_of_sub_eq_zero (norm_eq_zero.1 hz))) h
    rw [inner_sub_right, inner_sub_right, real_inner_comm x y, real_inner_self_eq_norm_mul_norm,
      real_inner_self_eq_norm_mul_norm, mul_sub_right_distrib, mul_sub_right_distrib,
      mul_self_mul_inv, mul_self_mul_inv, sub_eq_sub_iff_sub_eq_sub, ← mul_sub_left_distrib] at h
    by_cases hx0 : x = 0
    · rw [hx0, norm_zero, inner_zero_left, zero_mul, zero_sub, neg_eq_zero] at h
      rw [hx0, norm_zero, h]
    · by_cases hy0 : y = 0
      · rw [hy0, norm_zero, inner_zero_right, zero_mul, sub_zero] at h
        rw [hy0, norm_zero, h]
      · rw [inv_sub_inv (fun hz => hx0 (norm_eq_zero.1 hz)) fun hz => hy0 (norm_eq_zero.1 hz), ←
          neg_sub, ← mul_div_assoc, mul_comm, mul_div_assoc, ← mul_neg_one] at h
        symm
        by_contra hyx
        replace h := (mul_left_cancel₀ (sub_ne_zero_of_ne hyx) h).symm
        rw [real_inner_div_norm_mul_norm_eq_neg_one_iff, ← angle_eq_pi_iff] at h
        exact hpi h

/-- The cosine of the sum of two angles in a possibly degenerate
triangle (where two given sides are nonzero), vector angle form. -/
theorem cos_angle_sub_add_angle_sub_rev_eq_neg_cos_angle {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
    Real.cos (angle x (x - y) + angle y (y - x)) = -Real.cos (angle x y) := by
  by_cases hxy : x = y
  · rw [hxy, angle_self hy]
    simp
  · rw [Real.cos_add, cos_angle, cos_angle, cos_angle]
    have hxn : ‖x‖ ≠ 0 := fun h => hx (norm_eq_zero.1 h)
    have hyn : ‖y‖ ≠ 0 := fun h => hy (norm_eq_zero.1 h)
    have hxyn : ‖x - y‖ ≠ 0 := fun h => hxy (eq_of_sub_eq_zero (norm_eq_zero.1 h))
    apply mul_right_cancel₀ hxn
    apply mul_right_cancel₀ hyn
    apply mul_right_cancel₀ hxyn
    apply mul_right_cancel₀ hxyn
    have H1 :
      Real.sin (angle x (x - y)) * Real.sin (angle y (y - x)) * ‖x‖ * ‖y‖ * ‖x - y‖ * ‖x - y‖ =
        Real.sin (angle x (x - y)) * (‖x‖ * ‖x - y‖) *
          (Real.sin (angle y (y - x)) * (‖y‖ * ‖x - y‖)) := by
      ring
    have H2 :
      ⟪x, x⟫ * (⟪x, x⟫ - ⟪x, y⟫ - (⟪x, y⟫ - ⟪y, y⟫)) - (⟪x, x⟫ - ⟪x, y⟫) * (⟪x, x⟫ - ⟪x, y⟫) =
        ⟪x, x⟫ * ⟪y, y⟫ - ⟪x, y⟫ * ⟪x, y⟫ := by
      ring
    have H3 :
      ⟪y, y⟫ * (⟪y, y⟫ - ⟪x, y⟫ - (⟪x, y⟫ - ⟪x, x⟫)) - (⟪y, y⟫ - ⟪x, y⟫) * (⟪y, y⟫ - ⟪x, y⟫) =
        ⟪x, x⟫ * ⟪y, y⟫ - ⟪x, y⟫ * ⟪x, y⟫ := by
      ring
    rw [mul_sub_right_distrib, mul_sub_right_distrib, mul_sub_right_distrib, mul_sub_right_distrib,
      H1, sin_angle_mul_norm_mul_norm, norm_sub_rev x y, sin_angle_mul_norm_mul_norm,
      norm_sub_rev y x, inner_sub_left, inner_sub_left, inner_sub_right, inner_sub_right,
      inner_sub_right, inner_sub_right, real_inner_comm x y, H2, H3,
      Real.mul_self_sqrt (sub_nonneg_of_le (real_inner_mul_inner_self_le x y)),
      real_inner_self_eq_norm_mul_norm, real_inner_self_eq_norm_mul_norm,
      real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two]
    -- TODO(https://github.com/leanprover-community/mathlib4/issues/15486): used to be `field_simp [hxn, hyn, hxyn]`, but was really slow
    -- replaced by `simp only ...` to speed up. Reinstate `field_simp` once it is faster.
    simp (disch := field_simp_discharge) only [sub_div', div_div, mul_div_assoc',
      div_mul_eq_mul_div, div_sub', neg_div', neg_sub, eq_div_iff, div_eq_iff]
    ring

/-- The sine of the sum of two angles in a possibly degenerate
triangle (where two given sides are nonzero), vector angle form. -/
theorem sin_angle_sub_add_angle_sub_rev_eq_sin_angle {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
    Real.sin (angle x (x - y) + angle y (y - x)) = Real.sin (angle x y) := by
  by_cases hxy : x = y
  · rw [hxy, angle_self hy]
    simp
  · rw [Real.sin_add, cos_angle, cos_angle]
    have hxn : ‖x‖ ≠ 0 := fun h => hx (norm_eq_zero.1 h)
    have hyn : ‖y‖ ≠ 0 := fun h => hy (norm_eq_zero.1 h)
    have hxyn : ‖x - y‖ ≠ 0 := fun h => hxy (eq_of_sub_eq_zero (norm_eq_zero.1 h))
    apply mul_right_cancel₀ hxn
    apply mul_right_cancel₀ hyn
    apply mul_right_cancel₀ hxyn
    apply mul_right_cancel₀ hxyn
    have H1 :
      Real.sin (angle x (x - y)) * (⟪y, y - x⟫ / (‖y‖ * ‖y - x‖)) * ‖x‖ * ‖y‖ * ‖x - y‖ =
        Real.sin (angle x (x - y)) * (‖x‖ * ‖x - y‖) * (⟪y, y - x⟫ / (‖y‖ * ‖y - x‖)) * ‖y‖ := by
      ring
    have H2 :
      ⟪x, x - y⟫ / (‖x‖ * ‖y - x‖) * Real.sin (angle y (y - x)) * ‖x‖ * ‖y‖ * ‖y - x‖ =
        ⟪x, x - y⟫ / (‖x‖ * ‖y - x‖) * (Real.sin (angle y (y - x)) * (‖y‖ * ‖y - x‖)) * ‖x‖ := by
      ring
    have H3 :
      ⟪x, x⟫ * (⟪x, x⟫ - ⟪x, y⟫ - (⟪x, y⟫ - ⟪y, y⟫)) - (⟪x, x⟫ - ⟪x, y⟫) * (⟪x, x⟫ - ⟪x, y⟫) =
        ⟪x, x⟫ * ⟪y, y⟫ - ⟪x, y⟫ * ⟪x, y⟫ := by
      ring
    have H4 :
      ⟪y, y⟫ * (⟪y, y⟫ - ⟪x, y⟫ - (⟪x, y⟫ - ⟪x, x⟫)) - (⟪y, y⟫ - ⟪x, y⟫) * (⟪y, y⟫ - ⟪x, y⟫) =
        ⟪x, x⟫ * ⟪y, y⟫ - ⟪x, y⟫ * ⟪x, y⟫ := by
      ring
    rw [right_distrib, right_distrib, right_distrib, right_distrib, H1, sin_angle_mul_norm_mul_norm,
      norm_sub_rev x y, H2, sin_angle_mul_norm_mul_norm, norm_sub_rev y x,
      mul_assoc (Real.sin (angle x y)), sin_angle_mul_norm_mul_norm, inner_sub_left, inner_sub_left,
      inner_sub_right, inner_sub_right, inner_sub_right, inner_sub_right, real_inner_comm x y, H3,
      H4, real_inner_self_eq_norm_mul_norm, real_inner_self_eq_norm_mul_norm,
      real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two]
    -- TODO(https://github.com/leanprover-community/mathlib4/issues/15486): used to be `field_simp [hxn, hyn, hxyn]`, but was really slow
    -- replaced by `simp only ...` to speed up. Reinstate `field_simp` once it is faster.
    simp (disch := field_simp_discharge) only [mul_div_assoc', div_mul_eq_mul_div, div_div,
      sub_div', Real.sqrt_div', Real.sqrt_mul_self, add_div', div_add', eq_div_iff, div_eq_iff]
    ring

/-- The cosine of the sum of the angles of a possibly degenerate
triangle (where two given sides are nonzero), vector angle form. -/
theorem cos_angle_add_angle_sub_add_angle_sub_eq_neg_one {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
    Real.cos (angle x y + angle x (x - y) + angle y (y - x)) = -1 := by
  rw [add_assoc, Real.cos_add, cos_angle_sub_add_angle_sub_rev_eq_neg_cos_angle hx hy,
    sin_angle_sub_add_angle_sub_rev_eq_sin_angle hx hy, mul_neg, ← neg_add', add_comm, ← sq, ← sq,
    Real.sin_sq_add_cos_sq]

/-- The sine of the sum of the angles of a possibly degenerate
triangle (where two given sides are nonzero), vector angle form. -/
theorem sin_angle_add_angle_sub_add_angle_sub_eq_zero {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
    Real.sin (angle x y + angle x (x - y) + angle y (y - x)) = 0 := by
  rw [add_assoc, Real.sin_add, cos_angle_sub_add_angle_sub_rev_eq_neg_cos_angle hx hy,
    sin_angle_sub_add_angle_sub_rev_eq_sin_angle hx hy]
  ring

/-- The sum of the angles of a possibly degenerate triangle (where one of the
two given sides is nonzero), vector angle form. -/
theorem angle_add_angle_sub_add_angle_sub_eq_pi (x : V) {y : V} (hy : y ≠ 0) :
    angle x y + angle x (x - y) + angle y (y - x) = π := by
  by_cases hx : x = 0
  · simp [hx, hy]
  have hcos := cos_angle_add_angle_sub_add_angle_sub_eq_neg_one hx hy
  have hsin := sin_angle_add_angle_sub_add_angle_sub_eq_zero hx hy
  rw [Real.sin_eq_zero_iff] at hsin
  obtain ⟨n, hn⟩ := hsin
  symm at hn
  have h0 : 0 ≤ angle x y + angle x (x - y) + angle y (y - x) :=
    add_nonneg (add_nonneg (angle_nonneg _ _) (angle_nonneg _ _)) (angle_nonneg _ _)
  have h3lt : angle x y + angle x (x - y) + angle y (y - x) < π + π + π := by
    by_contra hnlt
    have hxy : angle x y = π := by
      by_contra hxy
      exact hnlt (add_lt_add_of_lt_of_le (add_lt_add_of_lt_of_le (lt_of_le_of_ne
        (angle_le_pi _ _) hxy) (angle_le_pi _ _)) (angle_le_pi _ _))
    rw [hxy] at hnlt
    rw [angle_eq_pi_iff] at hxy
    rcases hxy with ⟨hx, ⟨r, ⟨hr, hxr⟩⟩⟩
    rw [hxr, ← one_smul ℝ x, ← mul_smul, mul_one, ← sub_smul, one_smul, sub_eq_add_neg,
      angle_smul_right_of_pos _ _ (add_pos zero_lt_one (neg_pos_of_neg hr)), angle_self hx,
      add_zero] at hnlt
    apply hnlt
    rw [add_assoc]
    exact add_lt_add_left (lt_of_le_of_lt (angle_le_pi _ _) (lt_add_of_pos_right π Real.pi_pos)) _
  have hn0 : 0 ≤ n := by
    rw [hn, mul_nonneg_iff_left_nonneg_of_pos Real.pi_pos] at h0
    norm_cast at h0
  have hn3 : n < 3 := by
    rw [hn, show π + π + π = 3 * π by ring] at h3lt
    replace h3lt := lt_of_mul_lt_mul_right h3lt (le_of_lt Real.pi_pos)
    norm_cast at h3lt
  interval_cases n
  · simp [hn] at hcos
  · norm_num [hn]
  · simp [hn] at hcos

end InnerProductGeometry

namespace EuclideanGeometry

/-!
### Geometrical results on triangles in Euclidean affine spaces

This section develops some geometrical definitions and results on
(possibly degenerate) triangles in Euclidean affine spaces.
-/

open InnerProductGeometry
open scoped EuclideanGeometry

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- **Law of cosines** (cosine rule), angle-at-point form. -/
theorem dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle (p₁ p₂ p₃ : P) :
    dist p₁ p₃ * dist p₁ p₃ = dist p₁ p₂ * dist p₁ p₂ + dist p₃ p₂ * dist p₃ p₂ -
      2 * dist p₁ p₂ * dist p₃ p₂ * Real.cos (∠ p₁ p₂ p₃) := by
  rw [dist_eq_norm_vsub V p₁ p₃, dist_eq_norm_vsub V p₁ p₂, dist_eq_norm_vsub V p₃ p₂]
  unfold angle
  convert norm_sub_sq_eq_norm_sq_add_norm_sq_sub_two_mul_norm_mul_norm_mul_cos_angle
    (p₁ -ᵥ p₂ : V) (p₃ -ᵥ p₂ : V)
  · exact (vsub_sub_vsub_cancel_right p₁ p₃ p₂).symm
  · exact (vsub_sub_vsub_cancel_right p₁ p₃ p₂).symm

alias law_cos := dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle

/-- **Law of sines** (sine rule), angle-at-point form. -/
theorem sin_angle_mul_dist_eq_sin_angle_mul_dist (p₁ p₂ p₃ : P) :
    Real.sin (∠ p₁ p₂ p₃) * dist p₂ p₃ = Real.sin (∠ p₃ p₁ p₂) * dist p₃ p₁ := by
  simp only [dist_comm p₂ p₃, angle]
  rw [dist_eq_norm_vsub V p₃ p₂, dist_eq_norm_vsub V p₃ p₁, InnerProductGeometry.angle_comm,
    sin_angle_mul_norm_eq_sin_angle_mul_norm, vsub_sub_vsub_cancel_right, mul_eq_mul_right_iff]
  left
  rw [InnerProductGeometry.angle_comm, ← neg_vsub_eq_vsub_rev p₁ p₂, angle_neg_right,
    Real.sin_pi_sub]

alias law_sin := sin_angle_mul_dist_eq_sin_angle_mul_dist

/-- A variant of the law of sines, angle-at-point form. -/
theorem sin_angle_div_dist_eq_sin_angle_div_dist {p₁ p₂ p₃ : P} (h23 : p₂ ≠ p₃) (h31 : p₃ ≠ p₁) :
    Real.sin (∠ p₁ p₂ p₃) / dist p₃ p₁ = Real.sin (∠ p₃ p₁ p₂) / dist p₂ p₃ := by
  field_simp [dist_ne_zero.mpr h23, dist_ne_zero.mpr h31]
  exact law_sin _ _ _

/-- A variant of the law of sines, requiring that the points not be collinear. -/
theorem dist_eq_dist_mul_sin_angle_div_sin_angle {p₁ p₂ p₃ : P}
    (h : ¬Collinear ℝ ({p₁, p₂, p₃} : Set P)) :
    dist p₁ p₂ = dist p₃ p₁ * Real.sin (∠ p₂ p₃ p₁) / Real.sin (∠ p₁ p₂ p₃) := by
  have sin_gt_zero : 0 < Real.sin (∠ p₁ p₂ p₃) := by
    apply sin_pos_of_not_collinear h
  field_simp [sin_gt_zero]
  rw [mul_comm, mul_comm (dist p₃ p₁), law_sin]

/-- **Isosceles Triangle Theorem**: Pons asinorum, angle-at-point form. -/
theorem angle_eq_angle_of_dist_eq {p₁ p₂ p₃ : P} (h : dist p₁ p₂ = dist p₁ p₃) :
    ∠ p₁ p₂ p₃ = ∠ p₁ p₃ p₂ := by
  rw [dist_eq_norm_vsub V p₁ p₂, dist_eq_norm_vsub V p₁ p₃] at h
  unfold angle
  convert angle_sub_eq_angle_sub_rev_of_norm_eq h
  · exact (vsub_sub_vsub_cancel_left p₃ p₂ p₁).symm
  · exact (vsub_sub_vsub_cancel_left p₂ p₃ p₁).symm

/-- Converse of pons asinorum, angle-at-point form. -/
theorem dist_eq_of_angle_eq_angle_of_angle_ne_pi {p₁ p₂ p₃ : P} (h : ∠ p₁ p₂ p₃ = ∠ p₁ p₃ p₂)
    (hpi : ∠ p₂ p₁ p₃ ≠ π) : dist p₁ p₂ = dist p₁ p₃ := by
  unfold angle at h hpi
  rw [dist_eq_norm_vsub V p₁ p₂, dist_eq_norm_vsub V p₁ p₃]
  rw [← angle_neg_neg, neg_vsub_eq_vsub_rev, neg_vsub_eq_vsub_rev] at hpi
  rw [← vsub_sub_vsub_cancel_left p₃ p₂ p₁, ← vsub_sub_vsub_cancel_left p₂ p₃ p₁] at h
  exact norm_eq_of_angle_sub_eq_angle_sub_rev_of_angle_ne_pi h hpi

/-- The **sum of the angles of a triangle** (possibly degenerate, where two
given vertices are distinct), angle-at-point. -/
theorem angle_add_angle_add_angle_eq_pi {p₁ p₂ : P} (p₃ : P) (h : p₂ ≠ p₁) :
    ∠ p₁ p₂ p₃ + ∠ p₂ p₃ p₁ + ∠ p₃ p₁ p₂ = π := by
  rw [add_assoc, add_comm, add_comm (∠ p₂ p₃ p₁), angle_comm p₂ p₃ p₁]
  unfold angle
  rw [← angle_neg_neg (p₁ -ᵥ p₃), ← angle_neg_neg (p₁ -ᵥ p₂), neg_vsub_eq_vsub_rev,
    neg_vsub_eq_vsub_rev, neg_vsub_eq_vsub_rev, neg_vsub_eq_vsub_rev, ←
    vsub_sub_vsub_cancel_right p₃ p₂ p₁, ← vsub_sub_vsub_cancel_right p₂ p₃ p₁]
  exact angle_add_angle_sub_add_angle_sub_eq_pi _ fun he => h (vsub_eq_zero_iff_eq.1 he)

/-- The **sum of the angles of a triangle** (possibly degenerate, where the triangle is a line),
oriented angles at point. -/
theorem oangle_add_oangle_add_oangle_eq_pi [Module.Oriented ℝ V (Fin 2)]
    [Fact (Module.finrank ℝ V = 2)] {p₁ p₂ p₃ : P} (h21 : p₂ ≠ p₁) (h32 : p₃ ≠ p₂)
    (h13 : p₁ ≠ p₃) : ∡ p₁ p₂ p₃ + ∡ p₂ p₃ p₁ + ∡ p₃ p₁ p₂ = π := by
  simpa only [neg_vsub_eq_vsub_rev] using
    positiveOrientation.oangle_add_cyc3_neg_left (vsub_ne_zero.mpr h21) (vsub_ne_zero.mpr h32)
      (vsub_ne_zero.mpr h13)

/-- **Stewart's Theorem**. -/
theorem dist_sq_mul_dist_add_dist_sq_mul_dist (a b c p : P) (h : ∠ b p c = π) :
    dist a b ^ 2 * dist c p + dist a c ^ 2 * dist b p =
    dist b c * (dist a p ^ 2 + dist b p * dist c p) := by
  rw [pow_two, pow_two, law_cos a p b, law_cos a p c,
    eq_sub_of_add_eq (angle_add_angle_eq_pi_of_angle_eq_pi a h), Real.cos_pi_sub,
    dist_eq_add_dist_of_angle_eq_pi h]
  ring

/-- **Apollonius's Theorem**. -/
theorem dist_sq_add_dist_sq_eq_two_mul_dist_midpoint_sq_add_half_dist_sq (a b c : P) :
    dist a b ^ 2 + dist a c ^ 2 = 2 * (dist a (midpoint ℝ b c) ^ 2 + (dist b c / 2) ^ 2) := by
  by_cases hbc : b = c
  · simp [hbc, midpoint_self, dist_self, two_mul]
  · let m := midpoint ℝ b c
    have : dist b c ≠ 0 := (dist_pos.mpr hbc).ne'
    have hm := dist_sq_mul_dist_add_dist_sq_mul_dist a b c m (angle_midpoint_eq_pi b c hbc)
    simp only [m, dist_left_midpoint, dist_right_midpoint, Real.norm_two] at hm
    calc
      dist a b ^ 2 + dist a c ^ 2 = 2 / dist b c * (dist a b ^ 2 *
        ((2 : ℝ)⁻¹ * dist b c) + dist a c ^ 2 * (2⁻¹ * dist b c)) := by
        -- TODO(https://github.com/leanprover-community/mathlib4/issues/15486): used to be `field_simp`, but was really slow
        -- replaced by `simp only ...` to speed up. Reinstate `field_simp` once it is faster.
        simp (disch := field_simp_discharge) only [inv_eq_one_div, div_mul_eq_mul_div, one_mul,
          mul_div_assoc', add_div', div_div, eq_div_iff]
        ring
      _ = 2 * (dist a (midpoint ℝ b c) ^ 2 + (dist b c / 2) ^ 2) := by
        rw [hm]
        -- TODO(https://github.com/leanprover-community/mathlib4/issues/15486): used to be `field_simp`, but was really slow
        -- replaced by `simp only ...` to speed up. Reinstate `field_simp` once it is faster.
        simp (disch := field_simp_discharge) only [inv_eq_one_div, div_mul_eq_mul_div, one_mul,
          mul_div_assoc', div_div, add_div', div_pow, eq_div_iff, div_eq_iff]
        ring

theorem dist_mul_of_eq_angle_of_dist_mul (a b c a' b' c' : P) (r : ℝ) (h : ∠ a' b' c' = ∠ a b c)
    (hab : dist a' b' = r * dist a b) (hcb : dist c' b' = r * dist c b) :
    dist a' c' = r * dist a c := by
  have h' : dist a' c' ^ 2 = (r * dist a c) ^ 2 := calc
    dist a' c' ^ 2 =
        dist a' b' ^ 2 + dist c' b' ^ 2 - 2 * dist a' b' * dist c' b' * Real.cos (∠ a' b' c') := by
      simp [pow_two, law_cos a' b' c']
    _ = r ^ 2 * (dist a b ^ 2 + dist c b ^ 2 - 2 * dist a b * dist c b * Real.cos (∠ a b c)) := by
      rw [h, hab, hcb]; ring
    _ = (r * dist a c) ^ 2 := by simp [pow_two, ← law_cos a b c]; ring
  by_cases hab₁ : a = b
  · have hab'₁ : a' = b' := by
      rw [← dist_eq_zero, hab, dist_eq_zero.mpr hab₁, mul_zero r]
    rw [hab₁, hab'₁, dist_comm b' c', dist_comm b c, hcb]
  · have h1 : 0 ≤ r * dist a b := by rw [← hab]; exact dist_nonneg
    have h2 : 0 ≤ r := nonneg_of_mul_nonneg_left h1 (dist_pos.mpr hab₁)
    exact (sq_eq_sq₀ dist_nonneg (mul_nonneg h2 dist_nonneg)).mp h'

end EuclideanGeometry
