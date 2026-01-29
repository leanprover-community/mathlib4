/-
Copyright (c) 2025 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.Geometry.Euclidean.Inversion.Basic
public import Mathlib.Geometry.Euclidean.Sphere.OrthRadius

/-!
# Poles and polars.

This file defines poles and polars for spheres in Euclidean spaces.

## Main definitions

* `EuclideanGeometry.Sphere.pole`: the inversion in the sphere of the point in an affine subspace
  closest to the center.

* `EuclideanGeometry.Sphere.polar`: the affine subspace orthogonal to the radius vector at a point
  and passing through its inversion in the sphere.

## Main theorems

* `EuclideanGeometry.Sphere.mem_polar_iff_mem_polar`: La Hire's theorem.

-/

@[expose] public section

noncomputable section

namespace EuclideanGeometry

namespace Sphere

open AffineSubspace Function
open scoped RealInnerProductSpace

variable {V P : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]

/-- The pole of an affine subspace is the inversion in the sphere of the point in that subspace
closest to the center. -/
def pole (s : Sphere P) (as : AffineSubspace ℝ P) [Nonempty as]
    [as.direction.HasOrthogonalProjection] : P :=
  inversion s.center s.radius (orthogonalProjection as s.center)

/-- The polar of a point is the affine subspace orthogonal to the radius vector at that point
and passing through its inversion in the sphere. -/
def polar (s : Sphere P) (p : P) : AffineSubspace ℝ P :=
  s.orthRadius (inversion s.center s.radius p)

instance (s : Sphere P) (p : P) : (s.polar p).direction.HasOrthogonalProjection := by
  rw [polar]
  infer_instance

instance (s : Sphere P) (p : P) : Nonempty (s.polar p) := by
  rw [polar]
  infer_instance

@[simp] lemma direction_polar {s : Sphere P} (hs : s.radius ≠ 0) (p : P) :
    (s.polar p).direction = (ℝ ∙ (p -ᵥ s.center))ᗮ := by
  rw [polar, direction_orthRadius, inversion_vsub_center,
    Submodule.orthogonalComplement_eq_orthogonalComplement]
  by_cases h : p = s.center
  · simp [h]
  · refine Submodule.span_singleton_smul_eq ?_ _
    simp [hs, h]

@[simp] lemma pole_polar {s : Sphere P} (hs : s.radius ≠ 0) (p : P) : s.pole (s.polar p) = p := by
  simp [pole, polar, hs]

lemma orthRadius_eq_polar_inversion {s : Sphere P} (hs : s.radius ≠ 0) (p : P) :
    s.orthRadius p = s.polar (inversion s.center s.radius p) := by
  simp [polar, hs]

@[simp] lemma polar_pole_orthRadius {s : Sphere P} (hs : s.radius ≠ 0) (p : P) :
    s.polar (s.pole (s.orthRadius p)) = s.orthRadius p := by
  simp [polar, pole, hs]

@[simp] lemma polar_center (s : Sphere P) : s.polar s.center = ⊤ := by
  simp [polar]

@[simp] lemma polar_zero_radius {s : Sphere P} (hs : s.radius = 0) (p : P) : s.polar p = ⊤ := by
  simp [polar, hs]

@[simp] lemma polar_eq_orthRadius_self_iff {s : Sphere P} (hs : 0 ≤ s.radius) {p : P} :
    s.polar p = s.orthRadius p ↔ p ∈ s ∨ p = s.center := by
  by_cases h : p = s.center
  · simp [h]
  simp only [polar, inversion, orthRadius_eq_orthRadius_iff, h, or_false]
  rw [← vsub_eq_zero_iff_eq, vadd_vsub_assoc, ← neg_vsub_eq_vsub_rev p s.center,
    ← neg_one_smul ℝ, ← add_smul, smul_eq_zero]
  simp only [← sub_eq_add_neg, sub_eq_zero, sq_eq_one_iff, vsub_eq_zero_iff_eq, h, or_false]
  refine ⟨fun hp ↦ ?_, fun hp ↦ ?_⟩
  · rcases hp with hp | hp
    · exact (eq_of_div_eq_one hp).symm
    · have hp' : 0 ≤ s.radius / dist p s.center := by positivity
      grind
  · rw [hp]
    refine .inl (div_self ?_)
    intro hr
    rw [mem_sphere] at hp
    simp_all

lemma mem_polar_iff_inner {s : Sphere P} {p₁ p₂ : P} : p₁ ∈ s.polar p₂ ↔
    s.radius = 0 ∨ p₂ = s.center ∨ ⟪p₁ -ᵥ s.center, p₂ -ᵥ s.center⟫ = s.radius ^ 2 := by
  by_cases hr : s.radius = 0
  · simp [hr]
  by_cases hp₂ : p₂ = s.center
  · simp [hp₂]
  simp only [hr, hp₂, false_or]
  simp_rw [polar, mem_orthRadius_iff_inner_left, inversion_vsub_center, inversion,
    vsub_vadd_eq_vsub_sub, inner_sub_left, real_inner_smul_left, real_inner_smul_right,
    real_inner_self_eq_norm_sq, ← dist_eq_norm_vsub]
  rw [← mul_eq_zero_iff_left (a := (dist p₂ s.center) ^ 2 / s.radius ^ 2) (by simp [hp₂, hr])]
  nth_rw 2 [← sub_eq_zero]
  convert Iff.rfl using 2
  field [dist_ne_zero.2 hp₂]

/-- **La Hire's theorem**: `p₁` lies on the polar of `p₂` if and only if `p₂` lies on the polar of
`p₁`. -/
theorem mem_polar_iff_mem_polar {s : Sphere P} {p₁ p₂ : P} (hp₁ : p₁ ≠ s.center)
    (hp₂ : p₂ ≠ s.center) : p₁ ∈ s.polar p₂ ↔ p₂ ∈ s.polar p₁ := by
  simp [mem_polar_iff_inner, real_inner_comm, hp₁, hp₂]

lemma mem_orthRadius_iff_mem_polar_of_mem {s : Sphere P} {p₁ p₂ : P} (hp₁ : p₁ ≠ s.center)
    (hp₂ : p₂ ∈ s) : p₁ ∈ s.orthRadius p₂ ↔ p₂ ∈ s.polar p₁ := by
  by_cases hr : s.radius = 0
  · rw [mem_sphere, hr, dist_eq_zero] at hp₂
    simp [hr, hp₂]
  rw [← (polar_eq_orthRadius_self_iff (radius_nonneg_of_mem hp₂)).2 (.inl hp₂)]
  refine mem_polar_iff_mem_polar hp₁ ?_
  rintro rfl
  simp_all

lemma mem_polar_of_mem_of_mem_orthRadius {s : Sphere P} {p₁ p₂ : P} (hp₂ : p₂ ∈ s)
    (h : p₁ ∈ s.orthRadius p₂) : p₂ ∈ s.polar p₁ := by
  by_cases hp₁ : p₁ = s.center
  · simp [hp₁]
  exact (mem_orthRadius_iff_mem_polar_of_mem hp₁ hp₂).1 h

lemma ncard_inter_polar_eq_two_of_radius_lt_dist [Fact (Module.finrank ℝ V = 2)] {s : Sphere P}
    (hs : 0 < s.radius) {p : P} (hp : s.radius < dist p s.center) :
    (s ∩ s.polar p : Set P).ncard = 2 := by
  refine ncard_inter_orthRadius_eq_two_of_dist_lt_radius ?_ ?_
  · simpa [dist_inversion_center, div_lt_iff₀ (hs.trans hp), pow_two, hs]
  · simp only [ne_eq, inversion_eq_center', hs.ne', or_false]
    rintro rfl
    rw [dist_self] at hp
    grind

end Sphere

end EuclideanGeometry
