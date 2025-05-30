import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-
Test:
- `cos_ofNat_mul_pi_div_ofNat_of_eq_sub_one`
- `cos_ofNat_mul_pi_div_ofNat_of_eq_two_mul_sub_one`
- `cos_ofNat_mul_pi_div_ofNat_of_eq_add_one`
- `sin_ofNat_mul_pi_div_ofNat_of_eq_sub_one`
- `sin_ofNat_mul_pi_div_ofNat_of_eq_two_mul_sub_one`
- `sin_ofNat_mul_pi_div_ofNat_of_eq_add_one`
- `tan_ofNat_mul_pi_div_ofNat_of_eq_sub_one`
- `tan_ofNat_mul_pi_div_ofNat_of_eq_two_mul_sub_one`
- `tan_ofNat_mul_pi_div_ofNat_of_eq_add_one`
are applied by `norm_num`
-/


open Real

-- cosine of multiples of π / 3

example : cos (2 * π / 3) = - 1 / 2 := by
  norm_num

example  : cos (4 * π / 3) = - 1 / 2 := by
  norm_num

example : cos (5 * π / 3) = 1 / 2 := by
  norm_num

-- sine of multiples of π / 3

example : sin (2 * π / 3) = √3 / 2 := by
  norm_num

example  : sin (4 * π / 3) = - √3 / 2 := by
  norm_num
  rw [neg_div']

example : sin (5 * π / 3) = - √3 / 2 := by
  norm_num
  rw [neg_div']

-- tan of multiples of π / 3

example : tan (2 * π / 3) = - √3 := by
  norm_num

example  : tan (4 * π / 3) = √3 := by
  norm_num

example : tan (5 * π / 3) = - √3 := by
  norm_num
