/-
Copyright (c) 2025 Ilmārs Cīrulis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ilmārs Cīrulis, Alex Meiburg
-/
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.NormedSpace.Normalize
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic

/-!
# The Triangle Inequality for Angles

This file contains proof that angles obey the triangle inequality.
-/

open InnerProductGeometry
open NormedSpace

open scoped RealInnerProductSpace

variable {V : Type*}
variable [NormedAddCommGroup V]
variable [InnerProductSpace ℝ V]

section UnitVectorAngles

/-- Gets the orthogonal direction of one vector relative to another. -/
private noncomputable def ortho (y x : V) : V := x - (ℝ ∙ y).starProjection x

private lemma inner_ortho_nonneg_of_norm_one {x y : V} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    0 ≤ ⟪x, ortho y x⟫ := by
  rw [ortho, Submodule.starProjection_unit_singleton _ hy, inner_sub_right,
    inner_self_eq_one_of_norm_one hx, real_inner_smul_right, real_inner_comm, sub_nonneg]
  grw [← sq, sq_le_one_iff_abs_le_one, abs_real_inner_le_norm, hx, hy, one_mul]

private lemma inner_normalize_ortho (x : V) {y : V} :
    ⟪y, normalize (ortho y x)⟫ = 0 := by
  simp only [NormedSpace.normalize, real_inner_smul_right, mul_eq_zero, inv_eq_zero, norm_eq_zero]
  right; rw [ortho, real_inner_comm, Submodule.starProjection_inner_eq_zero]
  exact Submodule.mem_span_singleton_self y

private lemma inner_normalized_ortho_sq_add_inner_sq_eq_one {x y : V}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ⟪x, normalize (ortho y x)⟫ ^ 2 + ⟪x, y⟫ ^ 2 = 1 := by
  rw [NormedSpace.normalize, real_inner_smul_right, ortho, inner_sub_right,
    Submodule.starProjection_unit_singleton _ hy, real_inner_smul_right]
  by_cases h₁ : x = y
  · simp_all
  by_cases h₂ : x = - y
  · simp_all
  rw [real_inner_self_eq_norm_sq, hx]
  have H1 : ‖x - ⟪y, x⟫ • y‖ ≠ 0 := by
    simp only [ne_eq, norm_eq_zero, sub_eq_zero]
    intro H2
    rw [H2, norm_smul, hy, Real.norm_eq_abs, mul_one] at hx
    apply eq_or_eq_neg_of_abs_eq at hx
    rcases hx with hx | hx <;> rw [hx] at H2 <;> simp_all
  field_simp
  rw [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right, inner_sub_right,
    real_inner_smul_right, real_inner_smul_left, real_inner_smul_right, real_inner_smul_left,
    real_inner_comm x y, real_inner_self_eq_norm_sq, hx, real_inner_self_eq_norm_sq, hy]
  ring

private lemma inner_ortho_right_eq_sin_angle {x y : V} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ⟪x, normalize (ortho y x)⟫ = Real.sin (angle x y) := by
  have H : ⟪x, normalize (ortho y x)⟫ ^ 2 = Real.sin (angle x y) ^ 2 := by
    simp [Real.sin_sq, ← inner_eq_cos_angle_of_norm_one hx hy,
      ← inner_normalized_ortho_sq_add_inner_sq_eq_one hx hy]
  rw [sq_eq_sq_iff_abs_eq_abs, abs_of_nonneg (sin_angle_nonneg x y)] at H
  have H0 : 0 ≤ ⟪x, normalize (ortho y x)⟫ := by
    rw [NormedSpace.normalize, real_inner_smul_right]
    exact Left.mul_nonneg (inv_nonneg_of_nonneg (norm_nonneg (ortho y x)))
      (inner_ortho_nonneg_of_norm_one hx hy)
  simp_all [abs_of_nonneg H0]

private lemma angle_le_angle_add_angle_aux {x y : V} (Hx : ‖x‖ = 1) (Hy : ‖y‖ = 1) :
    x = Real.cos (angle x y) • y + Real.sin (angle x y) • normalize (ortho y x) := by
  rw [← inner_ortho_right_eq_sin_angle Hx Hy, ← inner_eq_cos_angle_of_norm_one Hx Hy,
    ortho, Submodule.starProjection_unit_singleton _ Hy]
  by_cases hxy : x - ⟪x, y⟫ • y = 0
  · simp [hxy, real_inner_comm, ← sub_eq_zero]
  rw [NormedSpace.normalize, real_inner_smul_right, inner_sub_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, Hx, real_inner_comm y, ← sq, mul_smul, ← smul_assoc]
  norm_num
  have H : 1 - ⟪x, y⟫ ^ 2 ≠ 0 := by
    rw [sub_ne_zero, ne_comm, sq_ne_one_iff]
    constructor <;> contrapose! hxy
    · rw [inner_eq_one_iff_of_norm_one Hx Hy] at hxy
      simp [Hy, hxy, inner_self_eq_one_of_norm_one]
    · rw [inner_eq_neg_one_iff_of_norm_one Hx Hy] at hxy
      simp [Hy, hxy, inner_self_eq_one_of_norm_one]
  rw [← smul_assoc, smul_eq_mul]
  field_simp
  rw [sq, ← real_inner_self_eq_norm_sq]
  have H0 : ⟪x - ⟪x, y⟫ • y, x - ⟪x, y⟫ • y⟫ = 1 - ⟪x, y⟫ ^ 2 := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right, inner_self_eq_one_of_norm_one Hx,
      real_inner_smul_right, ← sq, real_inner_smul_left, real_inner_smul_left,
      real_inner_smul_right, inner_self_eq_one_of_norm_one Hy, real_inner_comm y x]
    ring
  rw [real_inner_comm x, H0]
  field_simp; simp

lemma angle_le_angle_add_angle_of_norm_one {x y z : V}
    (Hx : ‖x‖ = 1) (Hy : ‖y‖ = 1) (Hz : ‖z‖ = 1) :
    angle x z ≤ angle x y + angle y z := by
  rcases lt_or_ge Real.pi (angle x y + angle y z) with H | H
  · linarith [angle_le_pi x z]
  have H0 : 0 ≤ angle x y + angle y z :=
    add_nonneg (angle_nonneg x y) (angle_nonneg y z)
  have H1 : ⟪x, z⟫ = ⟪x, z⟫ := rfl
  nth_rw 2 [angle_le_angle_add_angle_aux Hx Hy, angle_le_angle_add_angle_aux Hz Hy] at H1
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    real_inner_comm y (normalize _), real_inner_self_eq_norm_sq, Hy,
    angle_comm z y, inner_normalize_ortho] at H1
  norm_num at H1
  rw [mul_comm (Real.cos (angle y z))] at H1
  have H2 : -1 ≤ ⟪normalize (ortho y x), normalize (ortho y z)⟫ := by
    by_cases H3 : ortho y x = 0
    · simp_all
    by_cases H4 : ortho y z = 0
    · simp_all
    exact neg_one_le_inner_of_norm_one
      (norm_normalize_eq_one_iff.mpr H3) (norm_normalize_eq_one_iff.mpr H4)
  have H3 := mul_nonneg (sin_angle_nonneg x y) (sin_angle_nonneg y z)
  have H4 : Real.cos (angle x y + angle y z) ≤ Real.cos (angle x z) := by
    rw [neg_le_iff_add_nonneg] at H2
    rw [Real.cos_add, ← inner_eq_cos_angle_of_norm_one Hx Hz, H1]
    linarith [mul_nonneg H3 H2]
  rwa [Real.strictAntiOn_cos.le_iff_ge ⟨H0, H⟩ ⟨angle_nonneg x z, angle_le_pi x z⟩] at H4

end UnitVectorAngles


/-- **Triangle inequality** for angles between vectors. -/
theorem InnerProductGeometry.angle_le_angle_add_angle (x y z : V) :
    angle x z ≤ angle x y + angle y z := by
  by_cases hx : x = 0
  · simpa [hx] using angle_nonneg y z
  by_cases hy : y = 0
  · simpa [hy] using angle_le_pi x z
  by_cases hz : z = 0
  · simpa [hz] using angle_nonneg x y
  simpa using angle_le_angle_add_angle_of_norm_one (norm_normalize_eq_one_iff.mpr hx)
    (norm_normalize_eq_one_iff.mpr hy) (norm_normalize_eq_one_iff.mpr hz)

namespace EuclideanGeometry

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- **Triangle inequality** for angles in Euclidean geometry. -/
theorem angle_le_angle_add_angle (p p₁ p₂ p₃ : P) : ∠ p₁ p p₃ ≤ ∠ p₁ p p₂ + ∠ p₂ p p₃ :=
  InnerProductGeometry.angle_le_angle_add_angle _ _ _

end EuclideanGeometry
