/-
Copyright (c) 2025 Ilmārs Cīrulis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ilmārs Cīrulis, Alex Meiburg
-/
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.NormedSpace.Normalize

/-!
# The Triangle Inequality (for angles between unit length vectors)

This file contains proof that angles between unit length vectors obey the triangle inequality.
(Adapted from: S. W. Drury (2001), Class Notes for 189-354A (pages 12-13).
https://www.math.mcgill.ca/drury/notes354.pdf, accessed 23/06/2025)
-/

namespace UnitVectorAngles

open InnerProductGeometry
open NormedSpace
open scoped RealInnerProductSpace

variable {V : Type*}
variable [NormedAddCommGroup V]
variable [InnerProductSpace ℝ V]


@[simp]
lemma inner_self_eq_one {x : V} (hx : ‖x‖ = 1) : ⟪x, x⟫ = 1 :=
  (inner_eq_one_iff_of_norm_one hx hx).mpr rfl

lemma neg_one_le_inner {x y : V} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) : -1 ≤ ⟪x, y⟫ := by
  have H := neg_le_of_abs_le (abs_real_inner_le_norm x y)
  rw [hx, hy] at H
  norm_num at H
  exact H

lemma neg_one_le_inner_normalize_normalize (x y : V) :
    (-1 : ℝ) ≤ ⟪normalize x, normalize y⟫ := by
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy]
  have H: ‖normalize x‖ = 1 := by
    simpa [norm_normalize_eq_one_iff]
  have H0: ‖normalize y‖ = 1 := by
    simpa [norm_normalize_eq_one_iff]
  exact neg_one_le_inner H H0

/-- Gets the orthogonal direction of one vector relative to another.
The definition is only for `y` such that `‖y‖ = 1`. -/
private noncomputable def ortho (y x : V) : V := x - ⟪x, y⟫ • y

private lemma inner_ortho_nonneg {x y : V} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) : 0 ≤ ⟪x, ortho y x⟫ := by
  rw [ortho, inner_sub_right, real_inner_smul_right, inner_self_eq_one hx]
  simp only [← sq, sub_nonneg, sq_le_one_iff_abs_le_one]
  have H := abs_real_inner_le_norm x y
  rw [hx, hy] at H
  norm_num at H
  exact H

@[simp]
private lemma inner_normalize_ortho (x : V) {y : V} (hy : ‖y‖ = 1) :
    ⟪y, normalize (ortho y x)⟫ = 0 := by
  rw [ortho, NormedSpace.normalize]
  simp [real_inner_smul_right, inner_sub_right, inner_self_eq_one hy,
    real_inner_comm]

private lemma inner_normalized_ortho_sq_add_inner_sq_eq_one {x y : V}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ⟪x, normalize (ortho y x)⟫ ^ 2 + ⟪x, y⟫ ^ 2 = 1 := by
  rw [ortho, NormedSpace.normalize, real_inner_smul_right, inner_sub_right, real_inner_smul_right]
  by_cases h₁ : x = y
  · simp [h₁, hy]
  by_cases h₂ : x = - y
  · simp [h₂, hy]
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

private lemma inner_ortho_right_eq_sin_angle {x y : V} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ⟪x, normalize (ortho y x)⟫ = Real.sin (angle x y) := by
  have H : ⟪x, normalize (ortho y x)⟫ ^ 2 = Real.sin (angle x y) ^ 2 := by
    simp [Real.sin_sq, ← inner_eq_cos_angle hx hy,
      ← inner_normalized_ortho_sq_add_inner_sq_eq_one hx hy]
  rw [sq_eq_sq_iff_abs_eq_abs] at H
  rw [abs_of_nonneg (sin_angle_nonneg x y)] at H
  have H0 : 0 ≤ ⟪x, normalize (ortho y x)⟫ := by
    rw [NormedSpace.normalize, real_inner_smul_right]
    have H1 := inner_ortho_nonneg hx hy
    have H2 := norm_nonneg (ortho y x)
    have H3 := inv_nonneg_of_nonneg H2
    exact Left.mul_nonneg H3 H1
  rw [abs_of_nonneg H0] at H
  exact H

private lemma angle_le_angle_add_angle_aux {x y : V} (Hx : ‖x‖ = 1) (Hy : ‖y‖ = 1) :
    x = Real.cos (angle x y) • y + Real.sin (angle x y) • normalize (ortho y x) := by
  rw [← inner_ortho_right_eq_sin_angle Hx Hy, ← inner_eq_cos_angle Hx Hy]
  by_cases hxy : x - ⟪x, y⟫ • y = 0
  · simp [ortho, hxy, ← sub_eq_zero]
  simp only [ortho]
  rw [NormedSpace.normalize, real_inner_smul_right, inner_sub_right, real_inner_smul_right]
  rw [real_inner_self_eq_norm_sq, Hx, ← sq, mul_smul, ← smul_assoc]
  norm_num
  have H : 1 - ⟪x, y⟫ ^ 2 ≠ 0 := by
    rw [sub_ne_zero, ne_comm, sq_ne_one_iff]
    constructor <;> contrapose! hxy
    · rw [inner_eq_one_iff_of_norm_one Hx Hy] at hxy
      simp [inner_self_eq_one, hxy, Hy]
    · rw [inner_eq_neg_one_iff_of_norm_one Hx Hy] at hxy
      simp [inner_self_eq_one, hxy, Hy]
  rw [← smul_assoc, smul_eq_mul]
  field_simp
  rw [sq, ← real_inner_self_eq_norm_sq]
  have H0 : ⟪x - ⟪x, y⟫ • y, x - ⟪x, y⟫ • y⟫ = 1 - ⟪x, y⟫ ^ 2 := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right, inner_self_eq_one Hx]
    rw [real_inner_smul_right, ← sq]
    field_simp
    rw [real_inner_smul_left, real_inner_smul_left, real_inner_smul_right]
    rw [inner_self_eq_one Hy, real_inner_comm y x]
    ring
  rw [H0]
  field_simp; simp only [one_smul, add_sub_cancel]

lemma angle_le_angle_add_angle {x y z : V} (Hx : ‖x‖ = 1) (Hy : ‖y‖ = 1) (Hz : ‖z‖ = 1) :
    angle x z ≤ angle x y + angle y z := by
  rcases lt_or_ge Real.pi (angle x y + angle y z) with H | H
  · linarith [angle_le_pi x z]
  have H0 : 0 ≤ angle x y + angle y z :=
    add_nonneg (angle_nonneg x y) (angle_nonneg y z)
  have H1 : ⟪x, z⟫ = ⟪x, z⟫ := rfl
  nth_rw 2 [angle_le_angle_add_angle_aux Hx Hy] at H1
  nth_rw 2 [angle_le_angle_add_angle_aux Hz Hy] at H1
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right] at H1
  simp only [real_inner_comm y (normalize _), real_inner_self_eq_norm_sq, Hy,
    angle_comm z y, inner_normalize_ortho] at H1
  norm_num at H1
  rw [mul_comm (Real.cos (angle y z))] at H1
  have H2 := neg_one_le_inner_normalize_normalize (ortho y x) (ortho y z)
  have H3 : 0 ≤ Real.sin (angle x y) * Real.sin (angle y z) :=
    mul_nonneg (sin_angle_nonneg x y) (sin_angle_nonneg y z)
  have H4 : Real.cos (angle x y + angle y z) ≤ Real.cos (angle x z) := by
    rw [Real.cos_add, ← inner_eq_cos_angle Hx Hz]
    rw [neg_le_iff_add_nonneg] at H2
    rw [H1]
    field_simp
    linarith [mul_nonneg H3 H2]
  rwa [Real.strictAntiOn_cos.le_iff_ge ⟨H0, H⟩ ⟨angle_nonneg x z, angle_le_pi x z⟩] at H4

end UnitVectorAngles
