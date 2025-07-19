import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.NormNum.NormNumI
import Mathlib.Data.ZMod.Basic

open Complex ComplexConjugate Real Qq

example : (1:ℂ) = 1 + 0 * I := by norm_num1
example : (I:ℂ) = 0 + 1 * I := by norm_num1
example : (1.5:ℂ) = 3 / 2 + 0 * I := by norm_num1
example : (1.0:ℂ) + 0 = 1 := by norm_num1
example : (1.0:ℂ) + 0.5 = 3/2 := by norm_num1
example : I + (3/2:ℂ) = 3/2 + I := by norm_num1
example : 1 * (2:ℂ) = 2 := by norm_num1
example : (1 + I) * (1 + I * I * I) = 2 := by norm_num1
example : (1 + 3.5 + I) * (1 + I) = 7 / 2 + 11 / 2 * I := by norm_num1
example : (3 + 4.5 * I)⁻¹ * (3 + 4.5 * I) = 1 := by norm_num1
example : -1 / (1 + I) = (I - 1) / 2 := by norm_num1
example : (I:ℂ) = 0 + 1 * I := by norm_num1
example : (1.5:ℂ) = ⟨3 / 2, 0⟩ := by conv_lhs => norm_numI
example : 0 + (1:ℂ) = 1 := by norm_num1
example : (1.0:ℂ) + 0 = 1 := by norm_num1
example : (1.0:ℂ) + 0.5 = 3/2 := by norm_num1
example : I + (3/2:ℂ) = 3/2 + I := by norm_num1

example : I + (3/2:ℂ) = 3/2 + I := by
  conv_lhs => norm_numI
  conv_rhs => norm_numI

example : 2 * (2.5:ℂ) = 5 := by norm_num1

example : (1 + I) * (1 + I * I * I) = 2 := by norm_num1

example : (1 + I) * (1 + I * I * I) = 2 := by norm_num1

example : (1 + I) * (1 + I * I * I) = 2 := by
  conv_lhs => norm_numI
  conv_rhs => norm_numI

example : (1 + 3.5 + I) * (1 + I) = 7 / 2 + 11 / 2 * I := by norm_num1
example : (3 + 4 * I)⁻¹ * (3 + 4 * I) = 1 := by norm_num1
example : -1 / (1 + I) = (I - 1) / 2 := by norm_num1
example : (1 + I) * (1 - I) = 2 := by norm_num1
example : (1 + 2 * I) - (1 + 2 * I) = 0 := by norm_num1
example : (conj (3 + 4 * I) : ℂ) * (3 + 4 * I) = 25 := by norm_num1
example : (3 + I : ℂ) ^ 2 = 8 + 6 * I := by norm_num1
example : (3 : ℂ) ^ 2 + (4 : ℂ) ^ 2 = 25 := by norm_num1

example : 3 + I ≠ I ^ 2 := by norm_num1
example : I ^ 2 ≠ 3 := by norm_num1
example : 1 + I ≠ 0 := by norm_num1
example : 1 + I ≠ 1 + 2 * I := by norm_num1

-- This is already pretty slow, but is 2x slower without the `binaryRec` implementation.`
example : I ^ 11 = -I := by norm_num

example : re ((1 + 3 * I)⁻¹) = 0.1 := by norm_num1
example : im ((1 + 3 * I)⁻¹) = -0.3 := by norm_num1
example : 10 * re ((1 + 3 * I)⁻¹) = 1 := by norm_num1

example : (37 : ℕ) + 5 = 42 := rfl
example : (37 : ℤ) + 5 = 42 := rfl
example : (37 : ℚ) + 5 = 42 := by norm_cast
example (x : ℤ) (hx : x = (42 : ℤ)) : (37 : ℝ) + 5 = x := by norm_num; rw [hx]; simp
example : (1 : ZMod 3) + 1 = -1 := by norm_num; rfl
/--
error: unsolved goals
⊢ False
-/
#guard_msgs in
example : I^3 + I = 1 := by norm_num1

/--
error: unsolved goals
⊢ False
-/
#guard_msgs in
example : 1 + I = 1 + 2 * I := by norm_num1

/--
error: unsolved goals
⊢ False
-/
#guard_msgs in
example : 2 * I ≠ 2 * I := by norm_num1

/--
error: unsolved goals
x : ℂ
⊢ x * I ≠ 0
-/
#guard_msgs in
-- this crashes if atom identification is buggy
example (x : ℂ) : x * I ≠ 0 := by norm_num1
