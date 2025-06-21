import Mathlib.Tactic.NormNum.Eq
import Mathlib.Algebra.Field.ZMod

example {K : Type*} [Field K] [CharP K 37] : ((3/4 : ℚ) + (5 : ℤ) : K) = 15 := by
  norm_num (char := [3, 37])

example {K : Type*} [Field K] [CharP K 37] : ((3/4 : ℚ) + (5 : ℤ) : K) = 15 := by
  norm_num (char := [3, 37])

example {K : Type*} [Field K] [CharP K 3] : ((3/4 : ℚ) + (5 : ℤ) : K) = 29 := by
  norm_num (char := [3, 37])

example {K : Type*} [Field K] [CharP K 3] : ((9/9 : ℚ) + (23/9 : ℕ) : K) ≠ 29 := by
  norm_num (char := [3, 37])

example : (↑(9/9 : ℚ) + ↑(23/9 : ℕ) : ZMod 3) ≠ 29 := by
  norm_num (char := [3, 37])
