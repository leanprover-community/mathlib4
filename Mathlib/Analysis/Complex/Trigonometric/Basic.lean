/-
Copyright (c) 2026 Xuanji Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuanji Li
-/
module

public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
Basic facts about the complex trigonometric functions, including periodicity and antiperiodicity.
-/

namespace Complex
open scoped Real

@[simp]
public theorem sinh_add_pi_I (z : ℂ) : sinh (z + π * I) = -sinh z := by
    simp [Complex.sinh_add, sinh_mul_I, cosh_mul_I]

@[simp]
public theorem sinh_sub_pi_I (z : ℂ) : sinh (z - π * I) = -sinh z := by
    simp [Complex.sinh_sub, sinh_mul_I, cosh_mul_I]

@[simp]
public theorem cosh_add_pi_I (z : ℂ) : cosh (z + π * I) = -cosh z := by
    simp [Complex.cosh_add, cosh_mul_I, sinh_mul_I]

@[simp]
public theorem cosh_sub_pi_I (z : ℂ) : cosh (z - π * I) = -cosh z := by
    simp [Complex.cosh_sub, cosh_mul_I, sinh_mul_I]

@[simp]
public theorem tanh_add_pi_I (z : ℂ) : tanh (z + π * I) = tanh z := by
  rw [Complex.tanh_eq_sinh_div_cosh, Complex.tanh_eq_sinh_div_cosh,
    sinh_add_pi_I, cosh_add_pi_I]; field_simp

@[simp]
public theorem tanh_sub_pi_I (z : ℂ) : tanh (z - π * I) = tanh z := by
  rw [Complex.tanh_eq_sinh_div_cosh, Complex.tanh_eq_sinh_div_cosh,
    sinh_sub_pi_I, cosh_sub_pi_I]; field_simp
