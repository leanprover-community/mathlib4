import Mathlib.Tactic.NormNum
import Mathlib.Data.Real.Basic

example : |(4 : ℤ)| = 4 := by norm_num1
example : |(4 : ℚ)| = 4 := by norm_num1
example : |(4 : ℝ)| = 4 := by norm_num1
example : |(-11 : ℤ)| = 11 := by norm_num1
example : |(3 : ℚ) / 7| = 3 / 7 := by norm_num1
example : |(1 : ℚ) / 5| < 1 / 3 := by norm_num1
example : |-(2 : ℚ) / 7| = 2 / 7 := by norm_num1
