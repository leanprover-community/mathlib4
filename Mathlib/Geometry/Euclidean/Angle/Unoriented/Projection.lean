/-
Copyright (c) 2025 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.Geometry.Euclidean.Angle.Unoriented.RightAngle
public import Mathlib.Geometry.Euclidean.Projection

/-!
# Angles and orthogonal projection.

This file proves lemmas relating to angles involving orthogonal projections.

-/

public section


namespace EuclideanGeometry

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
variable [NormedAddTorsor V P]

open scoped Real

@[simp] lemma angle_self_orthogonalProjection (p : P) {p' : P} {s : AffineSubspace ℝ P}
    [s.direction.HasOrthogonalProjection] (h : p' ∈ s) :
    haveI : Nonempty s := ⟨p', h⟩
    ∠ p (orthogonalProjection s p) p' = π / 2 := by
  have : Nonempty s := ⟨p', h⟩
  rw [angle, ← InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two]
  exact Submodule.inner_left_of_mem_orthogonal (K := s.direction)
    (AffineSubspace.vsub_mem_direction h (orthogonalProjection_mem _))
    (vsub_orthogonalProjection_mem_direction_orthogonal _ _)

@[simp] lemma angle_orthogonalProjection_self (p : P) {p' : P} {s : AffineSubspace ℝ P}
    [s.direction.HasOrthogonalProjection] (h : p' ∈ s) :
    haveI : Nonempty s := ⟨p', h⟩
    ∠ p' (orthogonalProjection s p) p = π / 2 := by
  rw [angle_comm, angle_self_orthogonalProjection p h]

theorem dist_orthogonalProjection_eq_sin_mul_dist (p : P) {q : P} {s : AffineSubspace ℝ P}
    [s.direction.HasOrthogonalProjection] (h : q ∈ s) :
    haveI : Nonempty s := ⟨q, h⟩
    dist p (orthogonalProjection s p) =
    Real.sin (∠ p q (orthogonalProjection s p).val) * dist p q := by
  rw [angle_comm]
  refine (sin_angle_mul_dist_of_angle_eq_pi_div_two ?_).symm
  exact angle_self_orthogonalProjection p h

theorem dist_orthogonalProjection_eq_sin_mul_dist_of_collinear {p q r : P}
    {s : AffineSubspace ℝ P} [s.direction.HasOrthogonalProjection] (hq : q ∈ s) (hr : r ∈ s)
    (hcollinear : haveI : Nonempty s := ⟨q, hq⟩; Collinear ℝ {(orthogonalProjection s p).val, q, r})
    (hqr : q ≠ r) :
    haveI : Nonempty s := ⟨q, hq⟩
    dist p (orthogonalProjection s p) = Real.sin (∠ p q r) * dist p q := by
  have : Nonempty s := ⟨q, hq⟩
  by_cases! hpq : orthogonalProjection s p = q
  · simp [← hpq, angle_self_orthogonalProjection p hr]
  rw [dist_orthogonalProjection_eq_sin_mul_dist p hq]
  rcases hcollinear.wbtw_or_wbtw_or_wbtw with h | h | h
  · suffices ∠ p q (orthogonalProjection s p).val = π - ∠ p q r by rw [this, Real.sin_pi_sub]
    rw [eq_sub_iff_add_eq, angle_add_angle_eq_pi_of_angle_eq_pi]
    exact Sbtw.angle₁₂₃_eq_pi ⟨h, hpq.symm, hqr⟩
  · rw [h.angle_eq_right _ hqr.symm]
  · rw [h.symm.angle_eq_right _ hpq]

end EuclideanGeometry
