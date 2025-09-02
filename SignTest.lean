import Mathlib

open Real

#check sign_mul_abs

--lemma sign_mul_abs
example (x : ℝ) : sign x * |x| = x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx <;>
  simp [*, sign_of_pos, sign_zero, sign_of_neg, abs_of_pos, abs_of_neg]

--lemma sign_mul
example (x y : ℝ) : (x * y).sign = x.sign * y.sign := by
  conv_rhs => unfold sign
  split_ifs <;>
  · sorry
