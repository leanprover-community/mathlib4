import Mathlib.Analysis.Complex.Exponential

example : (Real.exp 2) ^ (-2 : ℤ) = (Real.exp (-4)) := by
  rw [← Real.exp_int_mul]
  congr 1
  norm_num
