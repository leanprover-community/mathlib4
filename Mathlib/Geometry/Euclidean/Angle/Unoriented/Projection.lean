/-
Copyright (c) 2025 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
import Mathlib.Geometry.Euclidean.Projection

/-!
# Angles and orthogonal projection.

This file proves lemmas relating to angles involving orthogonal projections.

-/


namespace EuclideanGeometry

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
variable [NormedAddTorsor V P]

open scoped Real

@[simp] lemma angle_self_orthogonalProjection (p : P) {p' : P} {s : AffineSubspace ℝ P}
    [s.direction.HasOrthogonalProjection] (h : p' ∈ s) :
    haveI : Nonempty s := ⟨p', h⟩
    ∠ p (orthogonalProjection s p) p' = π / 2 := by
  haveI : Nonempty s := ⟨p', h⟩
  rw [angle, ← InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two]
  exact Submodule.inner_left_of_mem_orthogonal (K := s.direction)
    (AffineSubspace.vsub_mem_direction h (orthogonalProjection_mem _))
    (vsub_orthogonalProjection_mem_direction_orthogonal _ _)

@[simp] lemma angle_orthogonalProjection_self (p : P) {p' : P} {s : AffineSubspace ℝ P}
    [s.direction.HasOrthogonalProjection] (h : p' ∈ s) :
    haveI : Nonempty s := ⟨p', h⟩
    ∠ p' (orthogonalProjection s p) p = π / 2 := by
  rw [angle_comm, angle_self_orthogonalProjection p h]

end EuclideanGeometry
