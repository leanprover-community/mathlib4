/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic

/-!
# Angle between complex numbers

This file relates the Euclidean geometric notion of angle between complex numbers to the argument of
their quotient.

It also shows that the arc and chord distances between two unit complex numbers are equivalent up to
a factor of `π / 2`.

## TODO

Prove the corresponding results for oriented angles.

## Tags

arc-length, arc-distance
-/

open InnerProductGeometry Set
open scoped Real

namespace Complex
variable {a x y : ℂ}

/-- The angle between two non-zero complex numbers is the absolute value of the argument of their
quotient.

Note that this does not hold when `x` or `y` is `0` as the LHS is `π / 2` while the RHS is `0`. -/
lemma angle_eq_abs_arg (hx : x ≠ 0) (hy : y ≠ 0) : angle x y = |(x / y).arg| := by
  refine Real.arccos_eq_of_eq_cos (abs_nonneg _) (abs_arg_le_pi _) ?_
  rw [Real.cos_abs, Complex.cos_arg (div_ne_zero hx hy)]
  have := (map_ne_zero Complex.abs).2 hx
  have := (map_ne_zero Complex.abs).2 hy
  simp [div_eq_mul_inv, Complex.normSq_eq_norm_sq]
  field_simp
  ring

lemma angle_one_left (hy : y ≠ 0) : angle 1 y = |y.arg| := by simp [angle_eq_abs_arg, hy]
lemma angle_one_right (hx : x ≠ 0) : angle x 1 = |x.arg| := by simp [angle_eq_abs_arg, hx]

@[simp] lemma angle_mul_left (ha : a ≠ 0) (x y : ℂ) : angle (a * x) (a * y) = angle x y := by
  obtain rfl | hx := eq_or_ne x 0 <;> obtain rfl | hy := eq_or_ne y 0 <;>
    simp [angle_eq_abs_arg, mul_div_mul_left, *]

@[simp] lemma angle_mul_right (ha : a ≠ 0) (x y : ℂ) : angle (x * a) (y * a) = angle x y := by
  simp [mul_comm, angle_mul_left ha]

lemma angle_div_left_eq_angle_mul_right (a x y : ℂ) : angle (x / a) y = angle x (y * a) := by
  obtain rfl | ha := eq_or_ne a 0
  · simp
  · rw [← angle_mul_right ha, div_mul_cancel₀ _ ha]

lemma angle_div_right_eq_angle_mul_left (a x y : ℂ) : angle x (y / a) = angle (x * a) y := by
  rw [angle_comm, angle_div_left_eq_angle_mul_right, angle_comm]

lemma angle_exp_exp (x y : ℝ) :
    angle (exp (x * I)) (exp (y * I)) = |toIocMod Real.two_pi_pos (-π) (x - y)| := by
  simp_rw [angle_eq_abs_arg (exp_ne_zero _) (exp_ne_zero _), ← exp_sub, ← sub_mul, ← ofReal_sub,
    arg_exp_mul_I]

lemma angle_exp_one (x : ℝ) : angle (exp (x * I)) 1 = |toIocMod Real.two_pi_pos (-π) x| := by
  simpa using angle_exp_exp x 0

/-!
### Arc-length and chord-length are equivalent

This section shows that the arc and chord distances between two unit complex numbers are equivalent
up to a factor of `π / 2`.
-/

/-- Chord-length is a multiple of arc-length up to constants. -/
lemma norm_sub_mem_Icc_angle (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ‖x - y‖ ∈ Icc (2 / π * angle x y) (angle x y) := by
  clear a
  wlog h : y = 1
  · have := @this (x / y) 1 (by simp only [norm_div, hx, hy, div_one]) norm_one rfl
    rwa [angle_div_left_eq_angle_mul_right, div_sub_one, norm_div, hy, div_one, one_mul]
      at this
    rintro rfl
    simp at hy
  subst y
  rw [norm_eq_abs, abs_eq_one_iff'] at hx
  obtain ⟨θ, hθ, rfl⟩ := hx
  rw [angle_exp_one, exp_mul_I, add_sub_right_comm, (toIocMod_eq_self _).2]
  · norm_cast
    rw [norm_eq_abs, abs_add_mul_I]
    refine ⟨Real.le_sqrt_of_sq_le ?_, ?_⟩
    · rw [mul_pow, ← _root_.abs_pow, abs_sq]
      calc
        _ = 2 * (1 - (1 - 2 / π ^ 2 * θ ^ 2)) := by ring
        _ ≤ 2 * (1 - θ.cos) := by
            gcongr; exact Real.cos_quadratic_upper_bound <| abs_le.2 <| Ioc_subset_Icc_self hθ
        _  = _ := by linear_combination -θ.cos_sq_add_sin_sq
    · rw [Real.sqrt_le_left (by positivity), ← _root_.abs_pow, abs_sq]
      calc
        _ = 2 * (1 - θ.cos) := by linear_combination θ.cos_sq_add_sin_sq
        _ ≤ 2 * (1 - (1 - θ ^ 2 / 2)) := by gcongr; exact Real.one_sub_sq_div_two_le_cos
        _ = _ := by ring
  · convert hθ
    ring

/-- Chord-length is always less than arc-length. -/
lemma norm_sub_le_angle (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) : ‖x - y‖ ≤ angle x y :=
  (norm_sub_mem_Icc_angle hx hy).2

/-- Chord-length is always greater than a multiple of arc-length. -/
lemma mul_angle_le_norm_sub (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) : 2 / π * angle x y ≤ ‖x - y‖ :=
  (norm_sub_mem_Icc_angle hx hy).1

/-- Arc-length is always less than a multiple of chord-length. -/
lemma angle_le_mul_norm_sub (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) : angle x y ≤ π / 2 * ‖x - y‖ := by
  rw [← div_le_iff' <| by positivity, div_eq_inv_mul, inv_div]; exact mul_angle_le_norm_sub hx hy

end Complex
