/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic

/-!
# Angle between complex numbers

This file relates the Euclidean geometric notion of angle between complex numbers to the argument of
their quotient.

## TODO

Prove the corresponding results for oriented angles.

## Tags

arc-length, arc-distance
-/

open InnerProductGeometry
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

end Complex
