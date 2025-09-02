import Mathlib

open Real

namespace Real

#check sign_mul_abs

@[simp]
lemma sign_mul_abs (x : ℝ) : sign x * |x| = x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx <;>
  simp [*, sign_of_pos, sign_zero, sign_of_neg, abs_of_pos, abs_of_neg]


#check sign_mul

lemma sign_mul (x y : ℝ) : (x * y).sign = x.sign * y.sign := by
  rcases lt_trichotomy x 0 with (hx | hx | hx) <;> rcases lt_trichotomy y 0 with (hy | hy | hy) <;>
    simp [hx, hy, mul_pos_of_neg_of_neg, mul_neg_of_neg_of_pos, mul_neg_of_pos_of_neg,
      sign_of_pos, sign_zero, sign_of_neg]

end Real
