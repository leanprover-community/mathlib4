/-
Copyright (c) 2025 Ilmārs Cīrulis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ilmārs Cīrulis, Alex Meiburg
-/
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Mathlib.Analysis.InnerProductSpace.TemporaryName
import Mathlib.Analysis.NormedSpace.Normalized

/-!
# The Triangle Inequality for Spherical Angles in Unit Sphere

This file contains proof that spherical angles in unit sphere obey the triangle inequality.
-/

namespace UnitSphere

open InnerProductGeometry

open scoped RealInnerProductSpace

variable {V : Type*}
variable [NormedAddCommGroup V]
variable [InnerProductSpace ℝ V]


@[simp]
lemma inner_self_eq_one {x : V} (hx : ‖x‖ = 1) : ⟪x, x⟫ = 1 :=
  (inner_eq_one_iff_of_norm_one hx hx).mpr rfl

lemma neg_one_le_inner {x y : V} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) : -1 ≤ ⟪x, y⟫ := by
  have H := neg_norm_le_real_inner x y
  rw [hx, hy] at H
  norm_num at H
  exact H

lemma neg_one_le_inner_normalized_normalized (x y : V) :
    (-1 : ℝ) ≤ ⟪normalized x, normalized y⟫ := by
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy]
  have H: ‖normalized x‖ = 1 := by
    simpa [norm_normalized_eq_one_iff]
  have H0: ‖normalized y‖ = 1 := by
    simpa [norm_normalized_eq_one_iff]
  exact neg_one_le_inner H H0

/-- Gets the orthogonal direction of one vector relative to another. -/
noncomputable def ortho (x y : V) : V := x - ⟪x, y⟫ • y

lemma inner_ortho_nonneg {x y : V} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1): 0 ≤ ⟪x, ortho x y⟫ := by
  rw [ortho, inner_sub_right, real_inner_smul_right, inner_self_eq_one hx]
  simp only [← sq, sub_nonneg, sq_le_one_iff_abs_le_one]
  have H := abs_real_inner_le_norm x y
  rw [hx, hy] at H
  norm_num at H
  exact H

@[simp]
lemma inner_normalized_ortho (x : V) {y : V} (hy : ‖y‖ = 1): ⟪y, normalized (ortho x y)⟫ = 0 := by
  rw [ortho, normalized]
  field_simp [real_inner_smul_right, inner_sub_right, inner_self_eq_one hy, real_inner_comm]

lemma ortho_aux {x y : V} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ⟪x, normalized (ortho x y)⟫ ^ 2 + ⟪x, y⟫ ^ 2 = 1 := by
  rw [ortho, normalized, real_inner_smul_right, inner_sub_right, real_inner_smul_right]
  by_cases h₁ : x = y
  · simp [h₁, real_inner_self_eq_norm_sq, hy]
  by_cases h₂ : x = - y
  · simp [h₂, real_inner_self_eq_norm_sq, hy]
  rw [real_inner_self_eq_norm_sq, hx]
  have H1 : ‖x - ⟪x, y⟫ • y‖ ≠ 0 := by
    simp only [ne_eq, norm_eq_zero];
    intro H2; rw [sub_eq_zero] at H2
    rw [H2, norm_smul, hy] at hx
    simp only [Real.norm_eq_abs, mul_one] at hx
    apply eq_or_eq_neg_of_abs_eq at hx
    rcases hx with hx | hx
    · simp only [one_smul, hx] at H2; tauto
    · simp only [neg_smul, one_smul, hx] at H2; tauto
  field_simp
  rw [← real_inner_self_eq_norm_sq]
  rw [inner_sub_left, inner_sub_right, inner_sub_right]
  rw [real_inner_smul_right, real_inner_smul_left]
  rw [real_inner_smul_right, real_inner_smul_left]
  rw [real_inner_comm x y]
  rw [real_inner_self_eq_norm_sq, hx, real_inner_self_eq_norm_sq, hy]
  ring


lemma inner_eq_cos_angle {x y : V} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ⟪x, y⟫ = Real.cos (angle x y) := by
  simp [cos_angle, hx, hy]

lemma inner_ortho_right_eq_sin_angle {x y : V} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1):
    ⟪x, normalized (ortho x y)⟫ = Real.sin (angle x y) := by
  have H : ⟪x, normalized (ortho x y)⟫ ^ 2 = Real.sin (angle x y) ^ 2 := by
    simp [Real.sin_sq, ← inner_eq_cos_angle hx hy, ← ortho_aux hx hy]
  rw [sq_eq_sq_iff_abs_eq_abs] at H
  rw [abs_of_nonneg (sin_angle_nonneg x y)] at H
  have H0 : 0 ≤ ⟪x, normalized (ortho x y)⟫ := by
    rw [normalized, real_inner_smul_right]
    have H1 := inner_ortho_nonneg hx hy
    have H2 := norm_nonneg (ortho x y)
    have H3 := inv_nonneg_of_nonneg H2
    exact Left.mul_nonneg H3 H1
  rw [abs_of_nonneg H0] at H
  exact H

lemma angle_triangle_aux {x y : V} (Hx : ‖x‖ = 1) (Hy : ‖y‖ = 1) :
    x = Real.cos (angle x y) • y + Real.sin (angle x y) • normalized (ortho x y) := by
  rw [← inner_ortho_right_eq_sin_angle Hx Hy]
  rw [← inner_eq_cos_angle Hx Hy]
  by_cases hxy : x - ⟪x, y⟫ • y = 0
  · simp [ortho, Hy, hxy, Hx, ← sub_eq_zero, ← inner_eq_cos_angle Hx Hy]
  simp only [ortho, normalized_eq_self_of_norm_eq_one Hy]
  rw [normalized, real_inner_smul_right, inner_sub_right, real_inner_smul_right]
  rw [real_inner_self_eq_norm_sq, Hx, ← sq, mul_smul, ← smul_assoc]
  norm_num
  have H : 1 - ⟪x, y⟫ ^ 2 ≠ 0 := by
    rw [sub_ne_zero, ne_comm, sq_ne_one_iff]
    constructor <;> contrapose! hxy
    · simp [sub_eq_zero, ← inner_eq_sq_norm_iff Hx Hy, hxy]
    · simp [hxy, add_eq_zero_iff_eq_neg, ← inner_eq_neg_sq_norm_iff Hx Hy]
  rw [← smul_assoc]
  field_simp
  rw [← sq, ← real_inner_self_eq_norm_sq]
  have H0 : ⟪x - ⟪x, y⟫ • y, x - ⟪x, y⟫ • y⟫ = 1 - inner x y ^ 2 := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right, inner_self_eq_one Hx]
    rw [real_inner_smul_right, ← sq]
    field_simp
    rw [real_inner_smul_left, real_inner_smul_left, real_inner_smul_right]
    rw [inner_self_eq_one Hy, real_inner_comm y x]
    ring
  rw [H0]
  field_simp

lemma angle_triangle {x y z : V}
    (Hx : ‖x‖ = 1) (Hy : ‖y‖ = 1) (Hz : ‖z‖ = 1):
    angle x z ≤ angle x y + angle y z := by
  rcases lt_or_ge Real.pi (angle x y + angle y z) with H | H
  · linarith [angle_le_pi x z]
  have H0 : 0 ≤ angle x y + angle y z :=
    add_nonneg (angle_nonneg x y) (angle_nonneg y z)
  have H1 : ⟪x, z⟫ = ⟪x, z⟫ := rfl
  nth_rw 2 [angle_triangle_aux Hx Hy] at H1
  nth_rw 2 [angle_triangle_aux Hz Hy] at H1
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    inner_normalized_ortho, real_inner_comm y (ortho x y)] at H1
  simp only [real_inner_comm y (normalized _), real_inner_self_eq_norm_sq, Hy,
    angle_comm z y, inner_normalized_ortho] at H1
  norm_num at H1
  rw [mul_comm (Real.cos (angle y z))] at H1
  have H2 := neg_one_le_inner_normalized_normalized (ortho x y) (ortho z y)
  have H3 : 0 ≤ Real.sin (angle x y) * Real.sin (angle y z) :=
    mul_nonneg (sin_angle_nonneg x y) (sin_angle_nonneg y z)
  have H4 : Real.cos (angle x y + angle y z) ≤ Real.cos (angle x z) := by
    rw [Real.cos_add, ← inner_eq_cos_angle Hx Hz]
    rw [neg_le_iff_add_nonneg] at H2
    rw [H1]
    field_simp
    linarith [mul_nonneg H3 H2]
  rwa [Real.strictAntiOn_cos.le_iff_le ⟨H0, H⟩ ⟨angle_nonneg x z, angle_le_pi x z⟩] at H4

end UnitSphere
