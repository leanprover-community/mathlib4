import Mathlib.Tactic.NormNum.Ordinal

universe u

example : (2 : Ordinal.{0}) * 3 + 4 = 10 := by norm_num

example : ¬(15 : Ordinal.{4}) / 4 % 34 < 3 := by norm_num

example : (12 : Ordinal.{u}) ^ (2 : Ordinal.{u}) ^ (2 : ℕ) ≤
    (12 : Ordinal.{u}) ^ (2 : Ordinal.{u}) ^ (2 : ℕ) := by norm_num
