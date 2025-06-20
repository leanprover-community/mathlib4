/-
Copyright (c) 2025 Ilmārs Cīrulis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ilmārs Cīrulis, Alex Meiburg
-/
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
import Mathlib.Geometry.Euclidean.Angle.Unoriented.UnitSphereAngles
import Mathlib.Analysis.NormedSpace.Normalized

/-!
# The Triangle Inequality for Angles

This file contains proof that angles obey the triangle inequality.
-/

open InnerProductGeometry

open scoped RealInnerProductSpace

variable {V : Type*}
variable [NormedAddCommGroup V]
variable [InnerProductSpace ℝ V]

-- where to put these two?
@[simp]
lemma angle_normalized_left (x y : V) :
    angle (normalized x) y = angle x y := by
  by_cases hx : x = 0
  · simp [hx]
  replace hx : 0 < ‖x‖⁻¹ := by simp [hx]
  simp only [normalized, angle_smul_left_of_pos, hx, angle_smul_right_of_pos]

@[simp]
lemma angle_normalized_right (x y : V) :
    angle x (normalized y) = angle x y := by
  rw [angle_comm, angle_normalized_left, angle_comm]

/-- **Triangle inequality** for angles between vectors. -/
theorem InnerProductGeometry.angle_triangle (x y z : V) : angle x z ≤ angle x y + angle y z := by
  by_cases hx : x = 0
  · simpa [hx] using angle_nonneg y z
  by_cases hy : y = 0
  · simpa [hy] using angle_le_pi x z
  by_cases hz : z = 0
  · simpa [hz] using angle_nonneg x y
  have H := UnitSphereAngles.angle_triangle (norm_normalized_eq_one_iff.mpr hx)
    (norm_normalized_eq_one_iff.mpr hy) (norm_normalized_eq_one_iff.mpr hz)
  simp at H
  exact H


namespace EuclideanGeometry

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- **Triangle inequality** for spherical angles in Euclidean geometry. -/
theorem angle_triangle (p p₁ p₂ p₃ : P) : ∠ p₁ p p₃ ≤ ∠ p₁ p p₂ + ∠ p₂ p p₃ :=
  InnerProductGeometry.angle_triangle _ _ _

end EuclideanGeometry
