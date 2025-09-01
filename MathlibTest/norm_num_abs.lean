import Mathlib.Tactic.NormNum.Abs
import Mathlib.Data.Real.Basic

example : |(4 : ℤ)| = 4 := by
  norm_num1
  guard_target =ₛ (4:ℤ) = 4
  rfl

example : |(4 : ℚ)| = 4 := by
  norm_num1
  guard_target =ₛ (4:ℚ) = 4
  rfl

example : |(4 : ℝ)| = 4 := by
  norm_num1
  rfl

example : |(-11 : ℤ)| = 11 := by
  norm_num1
  guard_target =ₛ (11:ℤ) = 11
  rfl

example: |(3:ℚ) / 7| = 3 / 7 := by norm_num1

/-
example: |-(2:ℚ) / 7| = 2 / 7 := by norm_num1

example: |(1:ℚ) / 5| < 1 / 3 := by norm_num1
-/
