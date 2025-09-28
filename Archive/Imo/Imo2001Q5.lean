/-
Copyright (c) 2025 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
import Mathlib.Geometry.Euclidean.Triangle

/-!
# IMO 2001 Q5

Let `ABC` be a triangle. Let `AP` bisect `∠BAC` and let `BQ` bisect `∠ABC`, with `P` on `BC` and
`Q` on `AC`. If `AB + BP = AQ + QB` and `∠BAC = 60°`, what are the angles of the triangle?

# Solution

We follow the solution from https://web.evanchen.cc/exams/IMO-2001-notes.pdf.

Let `x = ∠ABQ = ∠QBC`; it must be in `(0°, 60°)`. By angle chasing and the law of sines we derive
```
1 + sin 30° / sin (150° - 2x) = (sin x + sin 60°) / sin (120° - x)
```
Solving this equation gives `x = 40°`, yielding `∠ABC = 80°` and `∠ACB = 40°`.
-/

open Affine EuclideanGeometry
open scoped Real

variable {V X : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace X] [NormedAddTorsor V X]

noncomputable section

namespace Imo2001Q5

variable (X) in
/-- The problem's configuration. -/
structure Setup where
  (A B C P Q : X)
  P_on_BC : Wbtw ℝ B P C
  AP_bisect_BAC : ∠ B A P = ∠ P A C
  Q_on_AC : Wbtw ℝ A Q C
  BQ_bisect_ABC : ∠ A B Q = ∠ Q B C
  dist_sum : dist A B + dist B P = dist A Q + dist Q B
  BAC_eq : ∠ B A C = π / 3

namespace Setup

variable (s : Setup X)

/-! ### Nondegeneracy properties and values of angles -/

lemma A_ne_B : s.A ≠ s.B := by
  by_contra h; have := s.BAC_eq
  rw [h, angle_self_left] at this; linarith [Real.pi_pos]

lemma A_ne_C : s.A ≠ s.C := by
  by_contra h; have := s.BAC_eq
  rw [h, angle_self_right] at this; linarith [Real.pi_pos]

lemma B_ne_C : s.B ≠ s.C := by
  by_contra h; have := s.BAC_eq
  rw [h, angle_self_of_ne s.A_ne_C.symm] at this; linarith [Real.pi_pos]

lemma not_collinear_BAC : ¬Collinear ℝ {s.B, s.A, s.C} := by
  simp_rw [collinear_iff_eq_or_eq_or_sin_eq_zero, not_or, s.A_ne_B.symm, s.A_ne_C.symm, s.BAC_eq,
    Real.sin_pi_div_three]
  simp

lemma BAP_eq : ∠ s.B s.A s.P = π / 6 := by
  have := angle_add_of_ne_of_ne s.A_ne_B s.A_ne_C s.P_on_BC
  rw [← s.AP_bisect_BAC, ← two_mul, s.BAC_eq] at this; grind

lemma PAC_eq : ∠ s.P s.A s.C = π / 6 := by
  have := angle_add_of_ne_of_ne s.A_ne_B s.A_ne_C s.P_on_BC
  rw [s.AP_bisect_BAC, ← two_mul, s.BAC_eq] at this; grind

lemma P_ne_B : s.P ≠ s.B := by
  by_contra h; have := s.BAP_eq
  rw [h, angle_self_of_ne s.A_ne_B.symm] at this; linarith [Real.pi_pos]

lemma P_ne_C : s.P ≠ s.C := by
  by_contra h; have := s.PAC_eq
  rw [h, angle_self_of_ne s.A_ne_C.symm] at this; linarith [Real.pi_pos]

lemma sbtw_BPC : Sbtw ℝ s.B s.P s.C := ⟨s.P_on_BC, s.P_ne_B, s.P_ne_C⟩

lemma BPC_eq : ∠ s.B s.P s.C = π := by rw [angle_eq_pi_iff_sbtw]; exact s.sbtw_BPC

/-- `x = ∠ABQ = ∠QBC`. This is the main angle in the solution and it suffices to show
this is `2 * π / 9`. -/
def x : ℝ := ∠ s.A s.B s.Q

lemma ABQ_eq : ∠ s.A s.B s.Q = s.x := rfl

lemma QBC_eq : ∠ s.Q s.B s.C = s.x := by rw [← s.BQ_bisect_ABC, s.ABQ_eq]

lemma ABC_eq : ∠ s.A s.B s.C = 2 * s.x := by
  have := angle_add_of_ne_of_ne s.A_ne_B.symm s.B_ne_C s.Q_on_AC
  rw [s.ABQ_eq, s.QBC_eq] at this; grind

lemma x_pos : 0 < s.x := by
  by_contra! h
  replace h : s.x = 0 := le_antisymm h (angle_nonneg ..)
  have col := s.ABC_eq; rw [h, mul_zero] at col
  replace col : Collinear ℝ {s.A, s.B, s.C} := by
    apply collinear_of_sin_eq_zero; rw [col, Real.sin_zero]
  apply s.not_collinear_BAC; convert col using 1; grind

lemma Q_ne_A : s.Q ≠ s.A := by
  by_contra h; have := s.ABQ_eq
  rw [h, angle_self_of_ne s.A_ne_B] at this; linarith [s.x_pos]

lemma Q_ne_C : s.Q ≠ s.C := by
  by_contra h; have := s.QBC_eq
  rw [h, angle_self_of_ne s.B_ne_C.symm] at this; linarith [s.x_pos]

lemma sbtw_AQC : Sbtw ℝ s.A s.Q s.C := ⟨s.Q_on_AC, s.Q_ne_A, s.Q_ne_C⟩

lemma AQC_eq : ∠ s.A s.Q s.C = π := by rw [angle_eq_pi_iff_sbtw]; exact s.sbtw_AQC

lemma ACB_eq : ∠ s.A s.C s.B = 2 * π / 3 - 2 * s.x := by
  have := angle_add_angle_add_angle_eq_pi s.A s.B_ne_C
  rw [angle_comm, s.ABC_eq, s.BAC_eq] at this; grind

lemma x_lt_pi_div_three : s.x < π / 3 := by
  by_contra! h
  have col : ∠ s.A s.C s.B = 0 := by linarith [s.ACB_eq, angle_nonneg s.A s.C s.B]
  replace col : Collinear ℝ {s.A, s.C, s.B} := by
    apply collinear_of_sin_eq_zero; rw [col, Real.sin_zero]
  apply s.not_collinear_BAC; convert col using 1; grind

lemma APB_eq : ∠ s.A s.P s.B = 5 * π / 6 - 2 * s.x := by
  have := angle_add_angle_add_angle_eq_pi s.P s.A_ne_B
  rw [s.BAP_eq, angle_comm s.P, angle_eq_angle_of_angle_eq_pi _ s.BPC_eq, s.ABC_eq] at this
  grind

lemma AQB_eq : ∠ s.A s.Q s.B = 2 * π / 3 - s.x := by
  have := angle_add_angle_add_angle_eq_pi s.Q s.A_ne_B
  rw [angle_eq_angle_of_angle_eq_pi _ s.AQC_eq, s.BAC_eq, angle_comm s.Q, s.ABQ_eq] at this
  grind

/-- A macro for applying the bounds on `x`, `x_pos` and `x_lt_pi_div_three`. -/
macro (name := bx) "bx" : tactic => `(tactic| linarith [s.x_pos, s.x_lt_pi_div_three])

/-! ### Trigonometric reduction using the law of sines -/

/-- `dist B P` in terms of `dist A B`. -/
lemma BP_by_AB :
    dist s.B s.P = Real.sin (π / 6) / Real.sin (5 * π / 6 - 2 * s.x) * dist s.A s.B := by
  rw [div_mul_eq_mul_div₀]; apply eq_div_of_mul_eq
  · refine (Real.sin_pos_of_pos_of_lt_pi ?_ ?_).ne' <;> bx
  rw [← s.APB_eq, mul_comm, dist_comm, sin_angle_mul_dist_eq_sin_angle_mul_dist, ← s.BAP_eq,
    dist_comm]

/-- `dist A Q` in terms of `dist A B`. -/
lemma AQ_by_AB :
    dist s.A s.Q = Real.sin s.x / Real.sin (2 * π / 3 - s.x) * dist s.A s.B := by
  rw [div_mul_eq_mul_div₀]; apply eq_div_of_mul_eq
  · refine (Real.sin_pos_of_pos_of_lt_pi ?_ ?_).ne' <;> bx
  rw [← s.AQB_eq, mul_comm, ← sin_angle_mul_dist_eq_sin_angle_mul_dist, angle_comm, s.ABQ_eq,
    dist_comm]

/-- `dist Q B` in terms of `dist A B`. -/
lemma QB_by_AB :
    dist s.Q s.B = Real.sin (π / 3) / Real.sin (2 * π / 3 - s.x) * dist s.A s.B := by
  rw [div_mul_eq_mul_div₀]; apply eq_div_of_mul_eq
  · refine (Real.sin_pos_of_pos_of_lt_pi ?_ ?_).ne' <;> bx
  rw [← s.AQB_eq, mul_comm, sin_angle_mul_dist_eq_sin_angle_mul_dist,
    angle_eq_angle_of_angle_eq_pi _ s.AQC_eq, s.BAC_eq, dist_comm]

/-- The key trigonometric equation for `x`. -/
lemma key_x_equation :
    1 + Real.sin (π / 6) / Real.sin (5 * π / 6 - 2 * s.x) =
    (Real.sin s.x + Real.sin (π / 3)) / Real.sin (2 * π / 3 - s.x) := by
  have := s.dist_sum
  rw [s.BP_by_AB, ← one_add_mul, s.AQ_by_AB, s.QB_by_AB, ← add_mul, ← add_div] at this
  exact mul_right_cancel₀ (dist_ne_zero.mpr s.A_ne_B) this

/-! ### Solving the trigonometric equation -/

lemma x_eq : s.x = 2 * π / 9 := by
  have work := s.key_x_equation
  rw [Real.sin_add_sin, show 2 * π / 3 - s.x = π - 2 * ((s.x + π / 3) / 2) by ring, Real.sin_pi_sub,
    Real.sin_two_mul, mul_div_mul_left] at work; swap
  · refine mul_ne_zero two_ne_zero (Real.sin_pos_of_pos_of_lt_pi ?_ ?_).ne' <;> bx
  rw [← eq_sub_iff_add_eq', div_sub_one] at work; swap
  · refine (Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩).ne' <;> bx
  rw [add_div, sub_div s.x, ← Real.two_mul_sin_mul_sin, show π / 3 / 2 = π / 6 by ring,
    Real.sin_pi_div_six, show 2 * Real.sin (s.x / 2) * (1 / 2) = Real.sin (s.x / 2) by ring] at work
  apply mul_eq_mul_of_div_eq_div at work; rotate_left
  · refine (Real.sin_pos_of_pos_of_lt_pi ?_ ?_).ne' <;> bx
  · refine (Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩).ne' <;> bx
  rw [one_div_mul_eq_div, div_eq_iff_mul_eq two_ne_zero, ← mul_rotate, Real.two_mul_sin_mul_sin,
    show s.x / 2 - (5 * π / 6 - 2 * s.x) = 5 * (s.x / 2) + π / 6 - π by ring, Real.cos_sub_pi,
    show s.x / 2 + (5 * π / 6 - 2 * s.x) = π - (3 * (s.x / 2) + π / 6) by ring, Real.cos_pi_sub,
    neg_sub_neg] at work
  rw [mul_div_assoc, mul_comm, ← div_eq_iff two_ne_zero]
  set y := s.x / 2
  have iden := Real.cos_add_cos (y + π / 6) (5 * y + π / 6)
  rw [← work, sub_add_cancel, show (y + π / 6 + (5 * y + π / 6)) / 2 = 3 * y + π / 6 by ring,
    show (y + π / 6 - (5 * y + π / 6)) / 2 = -(2 * y) by ring, Real.cos_neg, ← mul_rotate, eq_comm,
    mul_left_eq_self₀] at iden
  have notleft : Real.cos (2 * y) * 2 ≠ 1 := by
    unfold y; rw [mul_div_cancel₀ _ two_ne_zero]; by_contra h
    rw [← eq_div_iff_mul_eq two_ne_zero, ← Real.cos_pi_div_three] at h
    apply Real.injOn_cos ⟨s.x_pos.le, by bx⟩ ⟨by positivity, by bound⟩ at h
    exact s.x_lt_pi_div_three.ne h
  replace iden := iden.resolve_left notleft
  rw [← Real.cos_pi_div_two] at iden
  apply Real.injOn_cos ⟨by unfold y; bx, by unfold y; bx⟩ ⟨by positivity, by bound⟩ at iden
  grind

end Setup

theorem result (s : Setup X) : ∠ s.A s.B s.C = 4 * π / 9 ∧ ∠ s.A s.C s.B = 2 * π / 9 := by
  rw [s.ABC_eq, s.ACB_eq, s.x_eq]; constructor <;> ring

end Imo2001Q5
