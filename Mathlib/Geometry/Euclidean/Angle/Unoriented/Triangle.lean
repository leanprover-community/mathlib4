/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import Mathlib.Data.Real.StarOrdered
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# The Triangle Inequality for Spherical Angles

This file proves that spherical angles obey the triangle inequality, both in the sense of
`InnerProductGeometry.angle` (angles between vectors) and `EuclideanGeometry.angle`
(angles between points).
-/

open Real

namespace InnerProductGeometry

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {x y : V}

/-- **Triangle inequality** for spherical angles. -/
theorem angle_triangle (x y z : V) : angle x z ≤ angle x y + angle y z := by
  rcases le_or_gt (angle x y + angle y z) π with h|h
  · have h₁ := angle_nonneg x y
    have h₂ := angle_nonneg y z
    rw [← strictAntiOn_cos.le_iff_le ⟨by positivity, h⟩ ⟨angle_nonneg x z, angle_le_pi x z⟩]
    rw [cos_add, tsub_le_iff_right, add_comm, ← tsub_le_iff_right]
    apply le_of_sq_le_sq ?_  <| Left.mul_nonneg (sin_angle_nonneg x y) (sin_angle_nonneg y z)
    rw [mul_pow, Real.sin_sq, Real.sin_sq]
    by_cases h : (‖x‖ = 0 ∨ ‖y‖ = 0 ∨ ‖z‖ = 0)
    · rcases h with h|h|h
      all_goals simpa [angle, h] using Real.abs_cos_le_one _
    set θxy := cos (angle x y)
    set θxz := cos (angle x z)
    set θyz := cos (angle y z)
    suffices θxz * θxz ≤ 1 - θyz * θyz - θxy * θxy + θxy * θyz * θxz + θxz * θxy * θyz by
      linarith
    --Gram matrices are always positive semidefinite, and this is the determinant of a Gram matrix.
    let A : Matrix (Fin 3) (Fin 3) ℝ := !![1, θxy, θxz; θxy, 1, θyz; θxz, θyz, 1]
    suffices A.PosSemidef by
      simpa [Matrix.det_fin_three, A] using this.det_nonneg
    constructor
    · ext i j
      fin_cases i <;> fin_cases j <;> rfl
    · intro v
      convert real_inner_self_nonneg (x := (v 0 / ‖x‖) • x + (v 1 / ‖y‖) • y + (v 2 / ‖z‖) • z)
      push_neg at h
      have hx : 0 < ‖x‖ := lt_of_le_of_ne' (norm_nonneg x) h.1
      have hy : 0 < ‖y‖ := lt_of_le_of_ne' (norm_nonneg y) h.2.1
      have hz : 0 < ‖z‖ := lt_of_le_of_ne' (norm_nonneg z) h.2.2
      field_simp [A, θxy, θxz, θyz, real_inner_comm y x, real_inner_comm z, cos_angle,
        Matrix.vecHead, Matrix.vecTail,  inner_smul_right, inner_add_right, inner_add_left,
        real_inner_smul_left, real_inner_self_eq_norm_mul_norm]
      ring_nf
  · exact le_trans (angle_le_pi x z) h.le

end InnerProductGeometry

namespace EuclideanGeometry

open scoped EuclideanGeometry

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- **Triangle inequality** for spherical angles in Euclidean geometry. -/
theorem angle_triangle (p p₁ p₂ p₃ : P) : ∠ p₁ p p₃ ≤ ∠ p₁ p p₂ + ∠ p₂ p p₃ :=
  InnerProductGeometry.angle_triangle _ _ _

end EuclideanGeometry
