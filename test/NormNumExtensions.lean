import Mathlib.Tactic.NormNum.Prime

/-! # Testing extensions of `norm_num` -/

set_option profiler true
set_option trace.profiler true
-- set_option trace.Tactic.norm_num true

set_option maxRecDepth 8000 in
example : Nat.Prime (2 ^ 25 - 39) := by norm_num1
set_option maxRecDepth 20000 in
example : Nat.Prime (2 ^ 28 - 57) := by norm_num1

example : ¬ Nat.Prime 0 := by norm_num
example : ¬ Nat.Prime 1 := by norm_num
example : Nat.Prime 2 := by norm_num
example : Nat.Prime 3 := by norm_num
example : ¬ Nat.Prime 4 := by norm_num
example : Nat.Prime 5 := by norm_num
example : Nat.Prime 109 := by norm_num
example : Nat.Prime 1277 := by norm_num
example : ¬ Nat.Prime (10 ^ 100) := by norm_num
example : ¬ Nat.Prime ((2 ^ 19 - 1) * (2 ^ 25 - 39)) := by norm_num1
example : Nat.Prime (2 ^ 19 - 1) := by norm_num1

example : Nat.minFac 0 = 2 := by norm_num
example : Nat.minFac 1 = 1 := by norm_num
example : Nat.minFac 2 = 2 := by norm_num
example : Nat.minFac 3 = 3 := by norm_num
example : Nat.minFac 4 = 2 := by norm_num
example : Nat.minFac 121 = 11 := by norm_num
example : Nat.minFac 221 = 13 := by norm_num

example : ¬ Nat.Prime 912 := by norm_num
example : Nat.minFac 912 = 2 := by norm_num

example : ¬ Nat.Prime 681 := by norm_num
example : Nat.minFac 681 = 3 := by norm_num

example : ¬ Nat.Prime 728 := by norm_num
example : Nat.minFac 728 = 2 := by norm_num

example : ¬ Nat.Prime 248 := by norm_num
example : Nat.minFac 248 = 2 := by norm_num

example : ¬ Nat.Prime 682 := by norm_num
example : Nat.minFac 682 = 2 := by norm_num

example : ¬ Nat.Prime 115 := by norm_num
example : Nat.minFac 115 = 5 := by norm_num

example : ¬ Nat.Prime 824 := by norm_num
example : Nat.minFac 824 = 2 := by norm_num

example : ¬ Nat.Prime 942 := by norm_num
example : Nat.minFac 942 = 2 := by norm_num

example : ¬ Nat.Prime 34 := by norm_num
example : Nat.minFac 34 = 2 := by norm_num

example : ¬ Nat.Prime 754 := by norm_num
example : Nat.minFac 754 = 2 := by norm_num

example : ¬ Nat.Prime 663 := by norm_num
example : Nat.minFac 663 = 3 := by norm_num

example : ¬ Nat.Prime 923 := by norm_num
example : Nat.minFac 923 = 13 := by norm_num

example : ¬ Nat.Prime 77 := by norm_num
example : Nat.minFac 77 = 7 := by norm_num

example : ¬ Nat.Prime 162 := by norm_num
example : Nat.minFac 162 = 2 := by norm_num

example : ¬ Nat.Prime 669 := by norm_num
example : Nat.minFac 669 = 3 := by norm_num

example : ¬ Nat.Prime 476 := by norm_num
example : Nat.minFac 476 = 2 := by norm_num

example : Nat.Prime 251 := by norm_num
example : Nat.minFac 251 = 251 := by norm_num

example : ¬ Nat.Prime 129 := by norm_num
example : Nat.minFac 129 = 3 := by norm_num

example : ¬ Nat.Prime 471 := by norm_num
example : Nat.minFac 471 = 3 := by norm_num

example : ¬ Nat.Prime 851 := by norm_num
example : Nat.minFac 851 = 23 := by norm_num
