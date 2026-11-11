/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

meta import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic

namespace Inclusion.Tests

example : Real.exp (-100) < 1e-43 := by dyadic_interval [prec := 145]

example : ⌊Real.exp 30⌋ = 10686474581524 := by
  rw [Int.floor_eq_iff]; constructor <;> dyadic_interval [prec := 1]

example : ⌊Real.exp (Real.exp 2)⌋ = 1618 := by
  rw [Int.floor_eq_iff]; constructor <;> dyadic_interval [prec := 15]

example {x : ℝ} (hx : x ≤ 0) : Real.exp x ≤ 1 := by dyadic_interval

example {x : ℝ} (hx : 1 ≤ x) : 2 ≤ Real.exp x := by dyadic_interval [prec := 4]

example (x : ℝ) : 0 ≤ Real.exp x := by dyadic_interval

/-! The results of `Mathlib.Analysis.Complex.ExponentialBounds` on `exp` and `log 2`. Goals with a
division of reals are rewritten first, since `dyadic_interval` has no division for `ℝ` yet. -/

example : |Real.exp 1 - 2244083 / 825552| ≤ 1 / 10 ^ 10 := by
  simp only [abs_le, le_sub_iff_add_le, sub_le_iff_le_add]
  norm_num
  rw [div_le_iff₀ (by positivity), le_div_iff₀ (by positivity)]
  dyadic_interval [prec := 35]

example : |Real.exp 1 - 363916618873 / 133877442384| ≤ 1 / 10 ^ 20 := by
  simp only [abs_le, le_sub_iff_add_le, sub_le_iff_le_add]
  norm_num
  rw [div_le_iff₀ (by positivity), le_div_iff₀ (by positivity)]
  dyadic_interval [prec := 66]

example : 2.7182818283 < Real.exp 1 := by dyadic_interval [prec := 33]

example : Real.exp 1 < 2.7182818286 := by dyadic_interval [prec := 34]

example : 2 < Real.exp 1 := by dyadic_interval [prec := 1]

example : Real.exp 1 < 3 := by dyadic_interval [prec := 2]

example : ⌊Real.exp 1⌋ = 2 := by
  rw [Int.floor_eq_iff]
  dyadic_interval [prec := 2]

example : ⌈Real.exp 1⌉ = 3 := by
  rw [Int.ceil_eq_iff]
  dyadic_interval [prec := 1]

example : round (Real.exp 1) = 3 := by
  have h : (1 / 2 : ℝ) = 0.5 := by norm_num
  rw [round_eq, h, Int.floor_eq_iff]
  dyadic_interval [prec := 1]

example : 0.36787944116 < Real.exp (-1) := by dyadic_interval [prec := 37]

example : Real.exp (-1) < 0.3678794412 := by dyadic_interval [prec := 36]

example : Real.exp (-1) < 1 / 2 := by
  rw [lt_div_iff₀ (by positivity)]
  dyadic_interval [prec := 3]

example : 0.6931471803 < Real.log 2 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  dyadic_interval [prec := 32]

example : Real.log 2 < 0.6931471808 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  dyadic_interval [prec := 33]

example : |Real.log 2 - 287209 / 414355| ≤ 1 / 10 ^ 10 := by
  have h₁ : 0.6931471805 < Real.log 2 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    dyadic_interval [prec := 35]
  have h₂ : Real.log 2 < 0.6931471806 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num)]
    dyadic_interval [prec := 36]
  rw [abs_le]
  constructor <;> linarith

end Inclusion.Tests
