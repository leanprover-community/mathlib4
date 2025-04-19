/-
Copyright (c) 2025 Ilmārs Cīrulis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ilmārs Cīrulis
-/
import Mathlib.Data.Real.StarOrdered
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic

/-!
# The Triangle Inequality for Angles

This file contains proof that angles obey the triangle inequality.
-/

open InnerProductGeometry

variable {V : Type}
variable [NormedAddCommGroup V]
variable [InnerProductSpace ℝ V]

noncomputable def unit (x : V): V := ‖x‖⁻¹ • x

theorem norm_of_unit {x : V} (H : x ≠ 0) : ‖unit x‖ = 1 := by
  unfold unit; rw [norm_smul];
  simp only [norm_inv, norm_norm]
  have H0: ‖x‖ ≠ 0 := by simp only [ne_eq, norm_eq_zero]; exact H
  field_simp

theorem inner_product_of_units_as_cos {x y : V} (Hx : ‖x‖ = 1) (Hy : ‖y‖ = 1) :
    inner (𝕜 := ℝ) x y = Real.cos (angle x y) := by
  rw [cos_angle, Hx, Hy]; simp

theorem inner_sq_of_unit {x : V} (Hx : ‖x‖ = 1) : inner x x = (1 : ℝ) := by
  rw [inner_eq_one_iff_of_norm_one Hx Hx]

theorem angle_triangle_aux1 {x y : V} (Hx : ‖x‖ = 1) (Hy : ‖y‖ = 1) :
    let u := unit (x - inner (𝕜 := ℝ) x y • y)
    inner x u ^ 2 + inner x y ^ 2 = (1 : ℝ) := by
  intro u; unfold u unit
  rw [real_inner_smul_right, inner_sub_right, real_inner_smul_right]
  obtain H | H := em (x = y)
  · rw [H]; rw [inner_sq_of_unit Hy]; simp
  · obtain H0 | H0 := em (x = - y)
    · rw [H0]; simp [inner_sq_of_unit Hy]
    · rw [inner_sq_of_unit Hx]
      have H1: ‖x - inner (𝕜 := ℝ) x y • y‖ ≠ 0 := by
        simp only [ne_eq, norm_eq_zero];
        intro H2; rw [sub_eq_zero] at H2
        rw [H2, norm_smul, Hy] at Hx
        simp only [Real.norm_eq_abs, mul_one] at Hx
        apply eq_or_eq_neg_of_abs_eq at Hx
        obtain Hx | Hx := Hx
        · rw [Hx] at H2; simp only [one_smul] at H2; tauto
        · rw [Hx] at H2; simp only [neg_smul, one_smul] at H2; tauto
      field_simp; rw [<- real_inner_self_eq_norm_sq]
      rw [inner_sub_left, inner_sub_right, inner_sub_right]
      rw [real_inner_smul_right, real_inner_smul_left]
      rw [real_inner_smul_right, real_inner_smul_left]
      rw [real_inner_comm x y]
      rw [inner_sq_of_unit Hx, inner_sq_of_unit Hy]
      ring

theorem inner_product_with_proj_nonneg {x y : V} (Hx : ‖x‖ = 1) (Hy : ‖y‖ = 1) :
    (0 : ℝ) ≤ inner x (unit (x - inner (𝕜 := ℝ) x y • y)) := by
  unfold unit; rw [real_inner_smul_right]
  have H := norm_nonneg (x - inner (𝕜 := ℝ) x y • y)
  apply inv_nonneg_of_nonneg at H
  apply mul_nonneg H ?_
  rw [inner_sub_right, real_inner_smul_right, inner_sq_of_unit Hx, <- sq]
  simp only [sub_nonneg, sq_le_one_iff_abs_le_one];
  rw [inner_product_of_units_as_cos Hx Hy]
  exact Real.abs_cos_le_one (angle x y)

theorem sin_as_inner_product {x y: V} (Hx: ‖x‖ = 1) (Hy: ‖y‖ = 1) :
    let u := unit (x - inner (𝕜 := ℝ) x y • y)
    inner (𝕜 := ℝ) x u = Real.sin (angle x y) := by
  intro u; unfold u
  have H0 := angle_triangle_aux1 Hx Hy; simp only at H0
  nth_rw 2 [inner_product_of_units_as_cos Hx Hy] at H0
  rw [Real.cos_sq'] at H0
  have H0: Real.sin (angle x y) ^ 2 = inner x (unit (x - inner (𝕜 := ℝ) x y • y)) ^ 2 := by
    linarith
  rw [sq_eq_sq_iff_abs_eq_abs] at H0
  rw [abs_of_nonneg (inner_product_with_proj_nonneg Hx Hy)] at H0
  rw [abs_of_nonneg (sin_angle_nonneg x y)] at H0
  exact H0.symm

theorem eq_of_inner_eq_one {x y : V} (Hx : ‖x‖ = 1) (Hy : ‖y‖ = 1) (H : inner x y = (1 : ℝ)) :
    x = y := by
  rw [inner_product_of_units_as_cos Hx Hy] at H
  rw [cos_eq_one_iff_angle_eq_zero] at H
  rw [angle_eq_zero_iff] at H
  obtain ⟨H, r, H0, H1⟩ := H
  rw [H1, norm_smul, Hx] at Hy
  simp only [Real.norm_eq_abs, mul_one] at Hy
  rw [abs_of_pos H0] at Hy
  rw [Hy] at H1; simp only [one_smul] at H1
  exact H1.symm

theorem eq_neg_of_inner_eq_neg_one {x y : V} (Hx : ‖x‖ = 1) (Hy : ‖y‖ = 1)
    (H : inner x y = (-1 : ℝ)) :
    x = - y := by
  rw [inner_product_of_units_as_cos Hx Hy] at H
  rw [cos_eq_neg_one_iff_angle_eq_pi] at H
  rw [angle_eq_pi_iff] at H
  obtain ⟨H, r, H0, H1⟩ := H
  rw [H1, norm_smul, Hx] at Hy;
  simp only [Real.norm_eq_abs, mul_one] at Hy
  rw [abs_of_neg H0, neg_eq_iff_eq_neg] at Hy
  rw [Hy] at H1; simp only [neg_smul, one_smul] at H1; rw [H1]; simp

theorem angle_triangle_aux2 {x y : V} (Hx : ‖x‖ = 1) (Hy : ‖y‖ = 1) :
    let u := unit (x - inner (𝕜 := ℝ) x y • y)
    x = Real.cos (angle x y) • y + Real.sin (angle x y) • u := by
  simp only
  rw [<- sin_as_inner_product Hx Hy, <- inner_product_of_units_as_cos Hx Hy]
  unfold unit
  rw [real_inner_smul_right]
  rw [inner_sub_right, real_inner_smul_right]
  rw [inner_sq_of_unit Hx, <- sq]
  rw [<- smul_assoc]
  obtain H | H := em (‖x - inner (𝕜 := ℝ) x y • y‖ = 0)
  · simp only [H, inv_zero, zero_mul, smul_eq_mul, mul_zero, zero_smul, add_zero]
    simp only [norm_eq_zero] at H; rw [sub_eq_zero] at H; exact H
  · field_simp
    rw [<- sq, <- real_inner_self_eq_norm_sq]
    rw [inner_sub_left, inner_sub_right, inner_sub_right]
    rw [real_inner_smul_left, real_inner_smul_right]
    rw [real_inner_smul_left, real_inner_smul_right]
    rw [real_inner_comm x y]
    rw [inner_sq_of_unit Hx, inner_sq_of_unit Hy]
    simp only [mul_one, sub_self, sub_zero]
    have H1 : inner x y ≠ (1 : ℝ) := by
      intro H2; apply H; simp only [norm_eq_zero]; rw [H2]
      simp only [one_smul]; rw [sub_eq_zero]
      apply eq_of_inner_eq_one Hx Hy H2
    have H2 : inner x y ≠ (-1 : ℝ) := by
      intro H3; apply H; simp only [norm_eq_zero];
      simp only [H3, neg_smul, one_smul, sub_neg_eq_add]
      rw [add_eq_zero_iff_eq_neg]
      apply eq_neg_of_inner_eq_neg_one Hx Hy H3
    rw [<- sq]
    have H3: (1 : ℝ) - inner x y ^ 2 ≠ 0 := by
      intro H3; rw [sub_eq_zero] at H3; symm at H3
      simp only [sq_eq_one_iff] at H3; tauto
    field_simp

lemma proj_ortogonal_of_unit (x : V) {y : V} (Hy : ‖y‖ = 1):
    let u := unit (x - @inner ℝ V _ x y • y)
    inner y u = (0 : ℝ) := by
  simp only; unfold unit; rw [real_inner_smul_right]
  simp only [mul_eq_zero, inv_eq_zero, norm_eq_zero]
  rw [inner_sub_right, real_inner_smul_right]
  rw [inner_sq_of_unit Hy, real_inner_comm x y]
  simp

lemma ge_of_le_cos {x y : ℝ} (Hx : x ∈ Set.Icc 0 Real.pi) (Hy : y ∈ Set.Icc 0 Real.pi)
    (H : Real.cos x ≤ Real.cos y) : y ≤ x := by
  rw [<- Real.arccos_cos Hy.1 Hy.2, <- Real.arccos_cos Hx.1 Hx.2]
  obtain H0 | H0 := eq_or_lt_of_le H
  · rw [<- Real.arccos_cos Hy.1 Hy.2, <- Real.arccos_cos Hx.1 Hx.2, H0]
  · apply (Real.strictAntiOn_arccos (Real.cos_mem_Icc x) (Real.cos_mem_Icc y)) at H0
    linarith

lemma angle_eq_angle_of_units {x y : V} (Hx : x ≠ 0) (Hy : y ≠ 0):
    angle x y = angle (unit x) (unit y) := by
  have H : 0 < ‖x‖⁻¹ := by simp; exact Hx
  have H0 : 0 < ‖y‖⁻¹ := by simp; exact Hy
  rw [unit, unit, angle_smul_left_of_pos _ _ H, angle_smul_right_of_pos _ _ H0]

lemma neg_one_le_inner_product_of_units (x y : V): (-1 : ℝ) ≤ inner (unit x) (unit y) := by
  obtain H | H := em (x = 0)
  · rw [H]; unfold unit; simp
  · obtain H0 | H0 := em (y = 0)
    · rw [H0]; unfold unit; simp
    · rw [inner_product_of_units_as_cos (norm_of_unit H) (norm_of_unit H0)]
      apply Real.neg_one_le_cos

lemma angle_triangle_for_units {x y z : V} (Hx : ‖x‖ = 1) (Hy : ‖y‖ = 1) (Hz : ‖z‖ = 1):
    angle x z ≤ angle x y + angle y z := by
  obtain H | H := em (angle x y + angle y z ≤ Real.pi)
  · have H0: 0 ≤ angle x y + angle y z := by
      linarith [angle_nonneg x y, angle_nonneg y z]
    have H1: inner (𝕜 := ℝ) x z = inner x z := by rfl
    nth_rw 2 [angle_triangle_aux2 Hx Hy] at H1
    nth_rw 2 [angle_triangle_aux2 Hz Hy] at H1
    rw [inner_add_left, inner_add_right, inner_add_right] at H1
    rw [real_inner_smul_left, real_inner_smul_right] at H1
    rw [inner_sq_of_unit Hy] at H1; simp only [mul_one] at H1
    rw [real_inner_smul_left, real_inner_smul_right] at H1
    rw [proj_ortogonal_of_unit z Hy] at H1
    simp only [mul_zero, add_zero] at H1
    rw [real_inner_smul_left, real_inner_smul_right] at H1
    rw [real_inner_comm y, proj_ortogonal_of_unit x Hy] at H1
    simp only [mul_zero, zero_add] at H1
    rw [real_inner_smul_left, real_inner_smul_right] at H1
    have H2 :=
      neg_one_le_inner_product_of_units (x - inner (𝕜 := ℝ) x y • y) (z - inner (𝕜 := ℝ) z y • y)
    have H3: 0 ≤ Real.sin (angle x y) * Real.sin (angle y z) :=
      (mul_nonneg (sin_angle_nonneg x y) (sin_angle_nonneg y z))
    have H4: Real.cos (angle x y + angle y z) ≤ Real.cos (angle x z) := by
      rw [Real.cos_add, <- inner_product_of_units_as_cos Hx Hz, H1, angle_comm z y]
      simp only [tsub_le_iff_right]
      rw [add_assoc, le_add_iff_nonneg_right, <- mul_assoc]
      rw [<- mul_add_one]
      apply (mul_nonneg H3); linarith
    apply ge_of_le_cos ⟨H0, H⟩ ⟨angle_nonneg x z, angle_le_pi x z⟩ H4
  · linarith [angle_le_pi x z]

theorem angle_triangle (x y z : V): angle x z ≤ angle x y + angle y z := by
  obtain H | H := em (x = 0)
  · rw [H]; simp only [angle_zero_left, le_add_iff_nonneg_right]; apply angle_nonneg
  · obtain H0 | H0 := em (y = 0)
    · rw [H0]; simp only [angle_zero_right, angle_zero_left, add_halves]; apply angle_le_pi
    · obtain H1 | H1 := em (z = 0)
      · rw [H1]; simp only [angle_zero_right, le_add_iff_nonneg_left]; apply angle_nonneg
      · rw [angle_eq_angle_of_units H H1, angle_eq_angle_of_units H H0,
            angle_eq_angle_of_units H0 H1]
        have Hx := norm_of_unit H
        have Hy := norm_of_unit H0
        have Hz := norm_of_unit H1
        apply angle_triangle_for_units Hx Hy Hz
