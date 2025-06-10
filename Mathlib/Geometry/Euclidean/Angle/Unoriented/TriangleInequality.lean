/-
Copyright (c) 2025 Ilmārs Cīrulis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ilmārs Cīrulis
-/
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine

/-!
# The Triangle Inequality for Angles

This file contains proof that angles obey the triangle inequality.
-/

open InnerProductGeometry

open scoped RealInnerProductSpace

variable {V : Type*}
variable [NormedAddCommGroup V]
variable [InnerProductSpace ℝ V]

lemma inner_product_of_units_as_cos {x y : V} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ⟪x, y⟫ = Real.cos (angle x y) := by
  simp [cos_angle, hx, hy]

lemma inner_eq_sq_norm_iff {x y : V} {a : ℝ} (hx : ‖x‖ = a) (hy : ‖y‖ = a) :
    ⟪x, y⟫ = a^2 ↔ x = y := by
  constructor
  · intro h
    rw [← sub_eq_zero, ← inner_self_eq_zero (𝕜 := ℝ)]
    simp [inner_sub_right, real_inner_self_eq_norm_sq, real_inner_comm, *]
  · rintro rfl
    rw [← hx, real_inner_self_eq_norm_sq x]

lemma inner_eq_neg_sq_norm_iff {x y : V} {a : ℝ} (hx : ‖x‖ = a) (hy : ‖y‖ = a) :
    ⟪x, y⟫ = -a^2 ↔ x = -y := by
  constructor
  · intro h
    rw [← sub_eq_zero, ← inner_self_eq_zero (𝕜 := ℝ)]
    simp only [inner_sub_right, real_inner_self_eq_norm_sq, real_inner_comm, inner_neg_right, *]
    abel
  · rintro rfl
    rw [inner_neg_left, real_inner_self_eq_norm_sq, hy]

/-- The unit length vector from a given vector. Note that `unit 0 = 0`. -/
noncomputable def unit (x : V) : V := ‖x‖⁻¹ • x

@[simp]
theorem unit_zero : unit (0 : V) = 0 := by
  simp [unit]

@[simp]
lemma norm_of_unit {x : V} : ‖unit x‖ = 1 ↔ x ≠ 0 := by
  constructor
  · contrapose!
    rintro rfl
    simp
  · intro h
    simp [unit, norm_smul, show ‖x‖ ≠ 0 by simp [h]]

@[simp]
lemma unit_eq_id_of_norm_one {x : V} (h : ‖x‖ = 1) : unit x = x := by
  simp [unit, h]

@[simp]
theorem unit_unit (x : V) : unit (unit x) = unit x := by
  by_cases hx : x = 0
  · simp [hx]
  rw [← ne_eq, ← norm_of_unit] at hx
  simp [hx]

theorem unit_smul_of_pos {r : ℝ} (hr : 0 < r) (x : V) : unit (r • x) = unit x := by
  by_cases hx : x = 0
  · simp [hx]
  rw [unit, unit, smul_smul, norm_smul]
  congr
  field_simp [abs_of_pos hr]

lemma neg_one_le_inner_unit_unit (x y : V) : -1 ≤ ⟪unit x, unit y⟫ := by
  by_cases hx : x = 0
  · simp [hx, unit]
  by_cases hy : y = 0
  · simp [hy, unit]
  convert Real.neg_one_le_cos <| angle (unit x) (unit y)
  simp [inner_product_of_units_as_cos, hx, hy]

/-- Gets the orthogonal direction of one vector relative to another. -/
noncomputable def orthoDir (x y : V) : V := unit (x - ⟪x, unit y⟫ • unit y)

@[simp]
theorem zero_orthoDir (x : V) : orthoDir 0 x = 0 := by
  simp [orthoDir]

@[simp]
theorem orthoDir_zero (x : V) : orthoDir x 0 = unit x := by
  simp [orthoDir]

@[simp]
lemma inner_sub_smul_eq_zero (x : V) {y : V} :
    ⟪y, x - ⟪x, unit y⟫ • unit y⟫ = 0 := by
  by_cases hy : ‖y‖ = 0
  · simp [show y = 0 by simpa using hy]
  field_simp [unit, real_inner_smul_right, inner_sub_right, real_inner_comm x y,
    real_inner_self_eq_norm_mul_norm]

@[simp]
lemma inner_orthoDir_zero (x : V) {y : V} :
    ⟪y, orthoDir x y⟫ = 0 := by
  rw [orthoDir, unit]
  simp [real_inner_smul_right]

@[simp]
theorem orthoDir_unit_left (x y : V) : orthoDir (unit x) y = orthoDir x y := by
  by_cases hx : ‖x‖ = 0
  · simp [show x = 0 by simpa using hx]
  by_cases hy : ‖y‖ = 0
  · simp [show y = 0 by simpa using hy]
  simp only [orthoDir, unit.eq_def x, inner_smul_left, map_inv₀, conj_trivial, mul_smul, ← smul_sub]
  refine unit_smul_of_pos ?_ _
  rw [Right.inv_pos]
  exact lt_of_le_of_ne (norm_nonneg x) fun a ↦ hx a.symm

@[simp]
theorem orthoDir_unit_right (x y : V) : orthoDir x (unit y) = orthoDir x y := by
  simp [orthoDir]

lemma inner_orthoDir_nonneg (x y : V) :
    0 ≤ ⟪x, orthoDir x y⟫ := by
  wlog Hx : ‖x‖ = 1
  · by_cases Hx : x = 0
    · simp [Hx]
    · convert this (unit x) y (by simpa) using 0
      rw [orthoDir_unit_left, unit, real_inner_smul_left, mul_nonneg_iff_of_pos_left ?_]
      rwa [Right.inv_pos, norm_pos_iff]
  wlog Hy : ‖y‖ = 1
  · by_cases Hy : y = 0
    · simp [Hy, unit, inner_smul_right, real_inner_self_eq_norm_sq, Hx]
    · simpa using this (V := V) x (unit y) Hx (by simpa)
  rw [orthoDir, unit_eq_id_of_norm_one Hy, unit]
  rw [real_inner_smul_right]
  have H := norm_nonneg (x - ⟪x, y⟫ • y)
  apply mul_nonneg (inv_nonneg_of_nonneg H)
  rw [inner_sub_right, real_inner_smul_right, ← sq, real_inner_self_eq_norm_sq, Hx]
  simp only [one_pow, sub_nonneg, sq_le_one_iff_abs_le_one]
  rw [inner_product_of_units_as_cos Hx Hy]
  exact Real.abs_cos_le_one (angle x y)

lemma orthoDir_aux_1 {x y : V} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ⟪x, orthoDir x y⟫ ^ 2 + ⟪x, y⟫ ^ 2 = 1 := by
  rw [orthoDir, unit]
  simp only [unit_eq_id_of_norm_one hy]
  rw [real_inner_smul_right, inner_sub_right, real_inner_smul_right]
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
  field_simp; rw [← real_inner_self_eq_norm_sq]
  rw [inner_sub_left, inner_sub_right, inner_sub_right]
  rw [real_inner_smul_right, real_inner_smul_left]
  rw [real_inner_smul_right, real_inner_smul_left]
  rw [real_inner_comm x y]
  rw [real_inner_self_eq_norm_sq, hx, real_inner_self_eq_norm_sq, hy]
  ring

--Angle-specific stuff

@[simp]
lemma angle_unit_left (x y : V) :
    angle (unit x) y = angle x y := by
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy]
  replace hx : 0 < ‖x‖⁻¹ := by simp [hx]
  replace hy : 0 < ‖y‖⁻¹ := by simp [hy]
  simp only [unit, angle_smul_left_of_pos, hx, angle_smul_right_of_pos, hy]

@[simp]
lemma angle_unit_right (x y : V) :
    angle x (unit y) = angle x y := by
  rw [angle_comm, angle_unit_left, angle_comm]


lemma sin_as_inner_product {x y : V} (Hx : ‖x‖ = 1) :
    ⟪x, orthoDir x y⟫ = Real.sin (angle x y) := by
  wlog Hy : ‖y‖ = 1
  · by_cases Hy : y = 0
    · simp [Hy, unit, inner_smul_right, real_inner_self_eq_norm_sq, Hx]
    · simpa using this (V := V) (y := unit y) Hx (by simpa)
  have h : ⟪x, orthoDir x y⟫ ^ 2 = Real.sin (angle x y) ^ 2 := by
    simp [Real.sin_sq, ← inner_product_of_units_as_cos Hx Hy, ← orthoDir_aux_1 Hx Hy]
  simpa [sq_eq_sq_iff_abs_eq_abs, abs_of_nonneg, inner_orthoDir_nonneg, sin_angle_nonneg] using h

lemma angle_triangle_aux2 {x y : V} (Hx : ‖x‖ = 1) (Hy : ‖y‖ = 1) :
    x = Real.cos (angle x y) • y + Real.sin (angle x y) • orthoDir x y := by
  rw [← sin_as_inner_product Hx]
  rw [← inner_product_of_units_as_cos Hx Hy]
  by_cases hxy : x - ⟪x, y⟫ • y = 0
  · simp [orthoDir, Hy, hxy, Hx, ← sub_eq_zero, ← inner_product_of_units_as_cos Hx Hy]
  simp only [orthoDir, unit_eq_id_of_norm_one Hy]
  rw [unit, real_inner_smul_right, inner_sub_right, real_inner_smul_right]
  rw [real_inner_self_eq_norm_sq, Hx, ← sq, ← smul_assoc]
  have H3 : 1 - ⟪x, y⟫ ^ 2 ≠ 0 := by
    rw [sub_ne_zero, ne_comm, sq_ne_one_iff]
    constructor <;> contrapose! hxy
    · simp [sub_eq_zero, ← inner_eq_sq_norm_iff Hx Hy, hxy]
    · simp [hxy, add_eq_zero_iff_eq_neg, ← inner_eq_neg_sq_norm_iff Hx Hy]
  field_simp [← sq, ← real_inner_self_eq_norm_sq, orthoDir,
    inner_sub_left, inner_sub_right, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right,
    real_inner_comm x y, real_inner_self_eq_norm_sq (x := y), real_inner_self_eq_norm_sq (x := x),
      Hx, Hy]

private lemma angle_triangle_for_units {x y z : V} (Hx : ‖x‖ = 1) (Hy : ‖y‖ = 1) (Hz : ‖z‖ = 1):
    angle x z ≤ angle x y + angle y z := by
  rcases lt_or_ge Real.pi (angle x y + angle y z) with H | H
  · linarith [angle_le_pi x z]
  have H0 : 0 ≤ angle x y + angle y z :=
    add_nonneg (angle_nonneg x y) (angle_nonneg y z)
  have H1 : ⟪x, z⟫ = ⟪x, z⟫ := rfl
  nth_rw 2 [angle_triangle_aux2 Hx Hy] at H1
  nth_rw 2 [angle_triangle_aux2 Hz Hy] at H1
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    inner_orthoDir_zero, real_inner_comm y (orthoDir x y)] at H1
  simp only [real_inner_comm y (unit _), real_inner_self_eq_norm_sq, Hy, angle_comm z y] at H1
  have H2 : (-1 : ℝ) ≤ inner (orthoDir x y) (orthoDir z y) := by
    simpa [orthoDir, Hy] using neg_one_le_inner_unit_unit (x - ⟪x, y⟫ • y) (z - ⟪z, y⟫ • y)
  have H3 : 0 ≤ Real.sin (angle x y) * Real.sin (angle y z) :=
    mul_nonneg (sin_angle_nonneg x y) (sin_angle_nonneg y z)
  have H4: Real.cos (angle x y + angle y z) ≤ Real.cos (angle x z) := by
    rw [Real.cos_add, ← inner_product_of_units_as_cos Hx Hz]
    rw [neg_le_iff_add_nonneg] at H2
    linarith [mul_nonneg H3 H2]
  rwa [Real.strictAntiOn_cos.le_iff_le ⟨H0, H⟩ ⟨angle_nonneg x z, angle_le_pi x z⟩] at H4

/-- **Triangle inequality** for angles between vectors. -/
theorem InnerProductGeometry.angle_triangle (x y z : V) : angle x z ≤ angle x y + angle y z := by
  by_cases hx : x = 0
  · simpa [hx] using angle_nonneg y z
  by_cases hy : y = 0
  · simpa [hy] using angle_le_pi x z
  by_cases hz : z = 0
  · simpa [hz] using angle_nonneg x y
  simpa using angle_triangle_for_units (norm_of_unit.mpr hx)
    (norm_of_unit.mpr hy) (norm_of_unit.mpr hz)

namespace EuclideanGeometry

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- **Triangle inequality** for spherical angles in Euclidean geometry. -/
theorem angle_triangle (p p₁ p₂ p₃ : P) : ∠ p₁ p p₃ ≤ ∠ p₁ p p₂ + ∠ p₂ p p₃ :=
  InnerProductGeometry.angle_triangle _ _ _

end EuclideanGeometry
