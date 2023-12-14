import Mathlib.Tactic.NormNum.Pow

example : 11 ^ 987654318 % 987654319 = 1 := by
  norm_num
