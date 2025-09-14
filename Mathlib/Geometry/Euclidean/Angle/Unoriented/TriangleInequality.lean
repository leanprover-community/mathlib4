/-
Copyright (c) 2025 Ilmārs Cīrulis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ilmārs Cīrulis, Alex Meiburg
-/
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
import Mathlib.Analysis.NormedSpace.Normalize

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

@[simp]
lemma inner_self_eq_one {x : V} (hx : ‖x‖ = 1) : ⟪x, x⟫ = 1 :=
  (inner_eq_one_iff_of_norm_one hx hx).mpr rfl

lemma neg_one_le_inner {x y : V} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) : -1 ≤ ⟪x, y⟫ := by
  have H := neg_le_of_abs_le (abs_real_inner_le_norm x y)
  simp_all

lemma neg_one_le_inner_normalize_normalize (x y : V) :
    (-1 : ℝ) ≤ ⟪normalize x, normalize y⟫ := by
  by_cases hx : x = 0
  · simp_all
  by_cases hy : y = 0
  · simp_all
  have H: ‖normalize x‖ = 1 := norm_normalize_eq_one_iff.mpr hx
  have H0: ‖normalize y‖ = 1 := norm_normalize_eq_one_iff.mpr hy
  exact neg_one_le_inner H H0

/-- Gets the orthogonal direction of one vector relative to another.
The definition is only for `y` such that `‖y‖ = 1`. -/
private noncomputable def ortho (y x : V) : V := x - ⟪x, y⟫ • y

private lemma inner_ortho_nonneg {x y : V} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) : 0 ≤ ⟪x, ortho y x⟫ := by
  rw [ortho, inner_sub_right, real_inner_smul_right, inner_self_eq_one hx]
  rw [← sq, sub_nonneg, sq_le_one_iff_abs_le_one]
  have H := abs_real_inner_le_norm x y
  simp_all

@[simp]
private lemma inner_normalize_ortho (x : V) {y : V} (hy : ‖y‖ = 1) :
    ⟪y, normalize (ortho y x)⟫ = 0 := by
  rw [ortho, NormedSpace.normalize, real_inner_smul_right, inner_sub_right,
      real_inner_smul_right, inner_self_eq_one hy, real_inner_comm]
  simp

private lemma inner_normalized_ortho_sq_add_inner_sq_eq_one {x y : V}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ⟪x, normalize (ortho y x)⟫ ^ 2 + ⟪x, y⟫ ^ 2 = 1 := by
  rw [ortho, NormedSpace.normalize, real_inner_smul_right, inner_sub_right, real_inner_smul_right]
  by_cases h₁ : x = y
  · simp_all
  by_cases h₂ : x = - y
  · simp_all
  rw [real_inner_self_eq_norm_sq, hx]
  have H1 : ‖x - ⟪x, y⟫ • y‖ ≠ 0 := by
    simp only [ne_eq, norm_eq_zero];
    intro H2; rw [sub_eq_zero] at H2
    rw [H2, norm_smul, hy] at hx
    simp only [Real.norm_eq_abs, mul_one] at hx
    apply eq_or_eq_neg_of_abs_eq at hx
    rcases hx with hx | hx <;> rw [hx] at H2 <;> simp_all
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
  simp_all [cos_angle]

private lemma inner_ortho_right_eq_sin_angle {x y : V} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ⟪x, normalize (ortho y x)⟫ = Real.sin (angle x y) := by
  have H : ⟪x, normalize (ortho y x)⟫ ^ 2 = Real.sin (angle x y) ^ 2 := by
    simp [Real.sin_sq, ← inner_eq_cos_angle hx hy,
      ← inner_normalized_ortho_sq_add_inner_sq_eq_one hx hy]
  rw [sq_eq_sq_iff_abs_eq_abs, abs_of_nonneg (sin_angle_nonneg x y)] at H
  have H0 : 0 ≤ ⟪x, normalize (ortho y x)⟫ := by
    rw [NormedSpace.normalize, real_inner_smul_right]
    have H1 := inner_ortho_nonneg hx hy
    have H2 := norm_nonneg (ortho y x)
    have H3 := inv_nonneg_of_nonneg H2
    exact Left.mul_nonneg H3 H1
  simp_all [abs_of_nonneg H0]

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
      simp_all [inner_self_eq_one]
    · rw [inner_eq_neg_one_iff_of_norm_one Hx Hy] at hxy
      simp_all [inner_self_eq_one]
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
  field_simp; simp

lemma angle_le_angle_add_angle_of_norm_one {x y z : V}
    (Hx : ‖x‖ = 1) (Hy : ‖y‖ = 1) (Hz : ‖z‖ = 1) :
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
  have H3 := mul_nonneg (sin_angle_nonneg x y) (sin_angle_nonneg y z)
  have H4 : Real.cos (angle x y + angle y z) ≤ Real.cos (angle x z) := by
    rw [Real.cos_add, ← inner_eq_cos_angle Hx Hz]
    rw [neg_le_iff_add_nonneg] at H2
    rw [H1]
    field_simp
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
  have H := angle_le_angle_add_angle_of_norm_one
    (norm_normalize_eq_one_iff.mpr hx) (norm_normalize_eq_one_iff.mpr hy)
    (norm_normalize_eq_one_iff.mpr hz)
  simp at H
  exact H


namespace EuclideanGeometry

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- **Triangle inequality** for angles in Euclidean geometry. -/
theorem angle_le_angle_add_angle (p p₁ p₂ p₃ : P) : ∠ p₁ p p₃ ≤ ∠ p₁ p p₂ + ∠ p₂ p p₃ :=
  InnerProductGeometry.angle_le_angle_add_angle _ _ _

end EuclideanGeometry
