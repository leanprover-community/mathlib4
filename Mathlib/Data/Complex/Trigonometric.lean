/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir
-/
import Mathlib.Data.Complex.Exponential

/-!
# Trigonometric and hyperbolic trigonometric functions

This file contains the definitions of the sine, cosine, tangent,
hyperbolic sine, hyperbolic cosine, and hyperbolic tangent functions.

-/

open CauSeq Finset IsAbsoluteValue
open scoped ComplexConjugate

namespace Complex

noncomputable section

/-- The complex sine function, defined via `exp` -/
@[pp_nodot]
def sin (z : ℂ) : ℂ :=
  (exp (-z * I) - exp (z * I)) * I / 2

/-- The complex cosine function, defined via `exp` -/
@[pp_nodot]
def cos (z : ℂ) : ℂ :=
  (exp (z * I) + exp (-z * I)) / 2

/-- The complex tangent function, defined as `sin z / cos z` -/
@[pp_nodot]
def tan (z : ℂ) : ℂ :=
  sin z / cos z

/-- The complex cotangent function, defined as `cos z / sin z` -/
def cot (z : ℂ) : ℂ :=
  cos z / sin z

/-- The complex hyperbolic sine function, defined via `exp` -/
@[pp_nodot]
def sinh (z : ℂ) : ℂ :=
  (exp z - exp (-z)) / 2

/-- The complex hyperbolic cosine function, defined via `exp` -/
@[pp_nodot]
def cosh (z : ℂ) : ℂ :=
  (exp z + exp (-z)) / 2

/-- The complex hyperbolic tangent function, defined as `sinh z / cosh z` -/
@[pp_nodot]
def tanh (z : ℂ) : ℂ :=
  sinh z / cosh z

end

end Complex

namespace Real

open Complex

noncomputable section

/-- The real sine function, defined as the real part of the complex sine -/
@[pp_nodot]
nonrec def sin (x : ℝ) : ℝ :=
  (sin x).re

/-- The real cosine function, defined as the real part of the complex cosine -/
@[pp_nodot]
nonrec def cos (x : ℝ) : ℝ :=
  (cos x).re

/-- The real tangent function, defined as the real part of the complex tangent -/
@[pp_nodot]
nonrec def tan (x : ℝ) : ℝ :=
  (tan x).re

/-- The real cotangent function, defined as the real part of the complex cotangent -/
nonrec def cot (x : ℝ) : ℝ :=
  (cot x).re

/-- The real hypebolic sine function, defined as the real part of the complex hyperbolic sine -/
@[pp_nodot]
nonrec def sinh (x : ℝ) : ℝ :=
  (sinh x).re

/-- The real hypebolic cosine function, defined as the real part of the complex hyperbolic cosine -/
@[pp_nodot]
nonrec def cosh (x : ℝ) : ℝ :=
  (cosh x).re

/-- The real hypebolic tangent function, defined as the real part of
the complex hyperbolic tangent -/
@[pp_nodot]
nonrec def tanh (x : ℝ) : ℝ :=
  (tanh x).re

end

end Real

namespace Complex

variable (x y : ℂ)

theorem two_sinh : 2 * sinh x = exp x - exp (-x) :=
  mul_div_cancel₀ _ two_ne_zero

theorem two_cosh : 2 * cosh x = exp x + exp (-x) :=
  mul_div_cancel₀ _ two_ne_zero

@[simp]
theorem sinh_zero : sinh 0 = 0 := by simp [sinh]

@[simp]
theorem sinh_neg : sinh (-x) = -sinh x := by simp [sinh, exp_neg, (neg_div _ _).symm, add_mul]

private theorem sinh_add_aux {a b c d : ℂ} :
    (a - b) * (c + d) + (a + b) * (c - d) = 2 * (a * c - b * d) := by ring

theorem sinh_add : sinh (x + y) = sinh x * cosh y + cosh x * sinh y := by
  rw [← mul_right_inj' (two_ne_zero' ℂ), two_sinh, exp_add, neg_add, exp_add, eq_comm, mul_add, ←
    mul_assoc, two_sinh, mul_left_comm, two_sinh, ← mul_right_inj' (two_ne_zero' ℂ), mul_add,
    mul_left_comm, two_cosh, ← mul_assoc, two_cosh]
  exact sinh_add_aux

@[simp]
theorem cosh_zero : cosh 0 = 1 := by simp [cosh]

@[simp]
theorem cosh_neg : cosh (-x) = cosh x := by simp [add_comm, cosh, exp_neg]

private theorem cosh_add_aux {a b c d : ℂ} :
    (a + b) * (c + d) + (a - b) * (c - d) = 2 * (a * c + b * d) := by ring

theorem cosh_add : cosh (x + y) = cosh x * cosh y + sinh x * sinh y := by
  rw [← mul_right_inj' (two_ne_zero' ℂ), two_cosh, exp_add, neg_add, exp_add, eq_comm, mul_add, ←
    mul_assoc, two_cosh, ← mul_assoc, two_sinh, ← mul_right_inj' (two_ne_zero' ℂ), mul_add,
    mul_left_comm, two_cosh, mul_left_comm, two_sinh]
  exact cosh_add_aux

theorem sinh_sub : sinh (x - y) = sinh x * cosh y - cosh x * sinh y := by
  simp [sub_eq_add_neg, sinh_add, sinh_neg, cosh_neg]

theorem cosh_sub : cosh (x - y) = cosh x * cosh y - sinh x * sinh y := by
  simp [sub_eq_add_neg, cosh_add, sinh_neg, cosh_neg]

theorem sinh_conj : sinh (conj x) = conj (sinh x) := by
  rw [sinh, ← RingHom.map_neg, exp_conj, exp_conj, ← RingHom.map_sub, sinh, map_div₀, map_ofNat]

@[simp]
theorem ofReal_sinh_ofReal_re (x : ℝ) : ((sinh x).re : ℂ) = sinh x :=
  conj_eq_iff_re.1 <| by rw [← sinh_conj, conj_ofReal]

@[simp, norm_cast]
theorem ofReal_sinh (x : ℝ) : (Real.sinh x : ℂ) = sinh x :=
  ofReal_sinh_ofReal_re _

@[simp]
theorem sinh_ofReal_im (x : ℝ) : (sinh x).im = 0 := by rw [← ofReal_sinh_ofReal_re, ofReal_im]

theorem sinh_ofReal_re (x : ℝ) : (sinh x).re = Real.sinh x :=
  rfl

theorem cosh_conj : cosh (conj x) = conj (cosh x) := by
  rw [cosh, ← RingHom.map_neg, exp_conj, exp_conj, ← RingHom.map_add, cosh, map_div₀, map_ofNat]

theorem ofReal_cosh_ofReal_re (x : ℝ) : ((cosh x).re : ℂ) = cosh x :=
  conj_eq_iff_re.1 <| by rw [← cosh_conj, conj_ofReal]

@[simp, norm_cast]
theorem ofReal_cosh (x : ℝ) : (Real.cosh x : ℂ) = cosh x :=
  ofReal_cosh_ofReal_re _

@[simp]
theorem cosh_ofReal_im (x : ℝ) : (cosh x).im = 0 := by rw [← ofReal_cosh_ofReal_re, ofReal_im]

@[simp]
theorem cosh_ofReal_re (x : ℝ) : (cosh x).re = Real.cosh x :=
  rfl

theorem tanh_eq_sinh_div_cosh : tanh x = sinh x / cosh x :=
  rfl

@[simp]
theorem tanh_zero : tanh 0 = 0 := by simp [tanh]

@[simp]
theorem tanh_neg : tanh (-x) = -tanh x := by simp [tanh, neg_div]

theorem tanh_conj : tanh (conj x) = conj (tanh x) := by
  rw [tanh, sinh_conj, cosh_conj, ← map_div₀, tanh]

@[simp]
theorem ofReal_tanh_ofReal_re (x : ℝ) : ((tanh x).re : ℂ) = tanh x :=
  conj_eq_iff_re.1 <| by rw [← tanh_conj, conj_ofReal]

@[simp, norm_cast]
theorem ofReal_tanh (x : ℝ) : (Real.tanh x : ℂ) = tanh x :=
  ofReal_tanh_ofReal_re _

@[simp]
theorem tanh_ofReal_im (x : ℝ) : (tanh x).im = 0 := by rw [← ofReal_tanh_ofReal_re, ofReal_im]

theorem tanh_ofReal_re (x : ℝ) : (tanh x).re = Real.tanh x :=
  rfl

@[simp]
theorem cosh_add_sinh : cosh x + sinh x = exp x := by
  rw [← mul_right_inj' (two_ne_zero' ℂ), mul_add, two_cosh, two_sinh, add_add_sub_cancel, two_mul]

@[simp]
theorem sinh_add_cosh : sinh x + cosh x = exp x := by rw [add_comm, cosh_add_sinh]

@[simp]
theorem exp_sub_cosh : exp x - cosh x = sinh x :=
  sub_eq_iff_eq_add.2 (sinh_add_cosh x).symm

@[simp]
theorem exp_sub_sinh : exp x - sinh x = cosh x :=
  sub_eq_iff_eq_add.2 (cosh_add_sinh x).symm

@[simp]
theorem cosh_sub_sinh : cosh x - sinh x = exp (-x) := by
  rw [← mul_right_inj' (two_ne_zero' ℂ), mul_sub, two_cosh, two_sinh, add_sub_sub_cancel, two_mul]

@[simp]
theorem sinh_sub_cosh : sinh x - cosh x = -exp (-x) := by rw [← neg_sub, cosh_sub_sinh]

@[simp]
theorem cosh_sq_sub_sinh_sq : cosh x ^ 2 - sinh x ^ 2 = 1 := by
  rw [sq_sub_sq, cosh_add_sinh, cosh_sub_sinh, ← exp_add, add_neg_cancel, exp_zero]

theorem cosh_sq : cosh x ^ 2 = sinh x ^ 2 + 1 := by
  rw [← cosh_sq_sub_sinh_sq x]
  ring

theorem sinh_sq : sinh x ^ 2 = cosh x ^ 2 - 1 := by
  rw [← cosh_sq_sub_sinh_sq x]
  ring

theorem cosh_two_mul : cosh (2 * x) = cosh x ^ 2 + sinh x ^ 2 := by rw [two_mul, cosh_add, sq, sq]

theorem sinh_two_mul : sinh (2 * x) = 2 * sinh x * cosh x := by
  rw [two_mul, sinh_add]
  ring

theorem cosh_three_mul : cosh (3 * x) = 4 * cosh x ^ 3 - 3 * cosh x := by
  have h1 : x + 2 * x = 3 * x := by ring
  rw [← h1, cosh_add x (2 * x)]
  simp only [cosh_two_mul, sinh_two_mul]
  have h2 : sinh x * (2 * sinh x * cosh x) = 2 * cosh x * sinh x ^ 2 := by ring
  rw [h2, sinh_sq]
  ring

theorem sinh_three_mul : sinh (3 * x) = 4 * sinh x ^ 3 + 3 * sinh x := by
  have h1 : x + 2 * x = 3 * x := by ring
  rw [← h1, sinh_add x (2 * x)]
  simp only [cosh_two_mul, sinh_two_mul]
  have h2 : cosh x * (2 * sinh x * cosh x) = 2 * sinh x * cosh x ^ 2 := by ring
  rw [h2, cosh_sq]
  ring

@[simp]
theorem sin_zero : sin 0 = 0 := by simp [sin]

@[simp]
theorem sin_neg : sin (-x) = -sin x := by
  simp [sin, sub_eq_add_neg, exp_neg, (neg_div _ _).symm, add_mul]

theorem two_sin : 2 * sin x = (exp (-x * I) - exp (x * I)) * I :=
  mul_div_cancel₀ _ two_ne_zero

theorem two_cos : 2 * cos x = exp (x * I) + exp (-x * I) :=
  mul_div_cancel₀ _ two_ne_zero

theorem sinh_mul_I : sinh (x * I) = sin x * I := by
  rw [← mul_right_inj' (two_ne_zero' ℂ), two_sinh, ← mul_assoc, two_sin, mul_assoc, I_mul_I,
    mul_neg_one, neg_sub, neg_mul_eq_neg_mul]

theorem cosh_mul_I : cosh (x * I) = cos x := by
  rw [← mul_right_inj' (two_ne_zero' ℂ), two_cosh, two_cos, neg_mul_eq_neg_mul]

theorem tanh_mul_I : tanh (x * I) = tan x * I := by
  rw [tanh_eq_sinh_div_cosh, cosh_mul_I, sinh_mul_I, mul_div_right_comm, tan]

theorem cos_mul_I : cos (x * I) = cosh x := by rw [← cosh_mul_I]; ring_nf; simp

theorem sin_mul_I : sin (x * I) = sinh x * I := by
  have h : I * sin (x * I) = -sinh x := by
    rw [mul_comm, ← sinh_mul_I]
    ring_nf
    simp
  rw [← neg_neg (sinh x), ← h]
  apply Complex.ext <;> simp

theorem tan_mul_I : tan (x * I) = tanh x * I := by
  rw [tan, sin_mul_I, cos_mul_I, mul_div_right_comm, tanh_eq_sinh_div_cosh]

theorem sin_add : sin (x + y) = sin x * cos y + cos x * sin y := by
  rw [← mul_left_inj' I_ne_zero, ← sinh_mul_I, add_mul, add_mul, mul_right_comm, ← sinh_mul_I,
    mul_assoc, ← sinh_mul_I, ← cosh_mul_I, ← cosh_mul_I, sinh_add]

@[simp]
theorem cos_zero : cos 0 = 1 := by simp [cos]

@[simp]
theorem cos_neg : cos (-x) = cos x := by simp [cos, sub_eq_add_neg, exp_neg, add_comm]

theorem cos_add : cos (x + y) = cos x * cos y - sin x * sin y := by
  rw [← cosh_mul_I, add_mul, cosh_add, cosh_mul_I, cosh_mul_I, sinh_mul_I, sinh_mul_I,
    mul_mul_mul_comm, I_mul_I, mul_neg_one, sub_eq_add_neg]

theorem sin_sub : sin (x - y) = sin x * cos y - cos x * sin y := by
  simp [sub_eq_add_neg, sin_add, sin_neg, cos_neg]

theorem cos_sub : cos (x - y) = cos x * cos y + sin x * sin y := by
  simp [sub_eq_add_neg, cos_add, sin_neg, cos_neg]

theorem sin_add_mul_I (x y : ℂ) : sin (x + y * I) = sin x * cosh y + cos x * sinh y * I := by
  rw [sin_add, cos_mul_I, sin_mul_I, mul_assoc]

theorem sin_eq (z : ℂ) : sin z = sin z.re * cosh z.im + cos z.re * sinh z.im * I := by
  convert sin_add_mul_I z.re z.im; exact (re_add_im z).symm

theorem cos_add_mul_I (x y : ℂ) : cos (x + y * I) = cos x * cosh y - sin x * sinh y * I := by
  rw [cos_add, cos_mul_I, sin_mul_I, mul_assoc]

theorem cos_eq (z : ℂ) : cos z = cos z.re * cosh z.im - sin z.re * sinh z.im * I := by
  convert cos_add_mul_I z.re z.im; exact (re_add_im z).symm

theorem sin_sub_sin : sin x - sin y = 2 * sin ((x - y) / 2) * cos ((x + y) / 2) := by
  have s1 := sin_add ((x + y) / 2) ((x - y) / 2)
  have s2 := sin_sub ((x + y) / 2) ((x - y) / 2)
  rw [div_add_div_same, add_sub, add_right_comm, add_sub_cancel_right, add_self_div_two] at s1
  rw [div_sub_div_same, ← sub_add, add_sub_cancel_left, add_self_div_two] at s2
  rw [s1, s2]
  ring

theorem cos_sub_cos : cos x - cos y = -2 * sin ((x + y) / 2) * sin ((x - y) / 2) := by
  have s1 := cos_add ((x + y) / 2) ((x - y) / 2)
  have s2 := cos_sub ((x + y) / 2) ((x - y) / 2)
  rw [div_add_div_same, add_sub, add_right_comm, add_sub_cancel_right, add_self_div_two] at s1
  rw [div_sub_div_same, ← sub_add, add_sub_cancel_left, add_self_div_two] at s2
  rw [s1, s2]
  ring

theorem sin_add_sin : sin x + sin y = 2 * sin ((x + y) / 2) * cos ((x - y) / 2) := by
  simpa using sin_sub_sin x (-y)

theorem cos_add_cos : cos x + cos y = 2 * cos ((x + y) / 2) * cos ((x - y) / 2) := by
  calc
    cos x + cos y = cos ((x + y) / 2 + (x - y) / 2) + cos ((x + y) / 2 - (x - y) / 2) := ?_
    _ =
        cos ((x + y) / 2) * cos ((x - y) / 2) - sin ((x + y) / 2) * sin ((x - y) / 2) +
          (cos ((x + y) / 2) * cos ((x - y) / 2) + sin ((x + y) / 2) * sin ((x - y) / 2)) :=
      ?_
    _ = 2 * cos ((x + y) / 2) * cos ((x - y) / 2) := ?_
  · congr <;> field_simp
  · rw [cos_add, cos_sub]
  ring

theorem sin_conj : sin (conj x) = conj (sin x) := by
  rw [← mul_left_inj' I_ne_zero, ← sinh_mul_I, ← conj_neg_I, ← RingHom.map_mul, ← RingHom.map_mul,
    sinh_conj, mul_neg, sinh_neg, sinh_mul_I, mul_neg]

@[simp]
theorem ofReal_sin_ofReal_re (x : ℝ) : ((sin x).re : ℂ) = sin x :=
  conj_eq_iff_re.1 <| by rw [← sin_conj, conj_ofReal]

@[simp, norm_cast]
theorem ofReal_sin (x : ℝ) : (Real.sin x : ℂ) = sin x :=
  ofReal_sin_ofReal_re _

@[simp]
theorem sin_ofReal_im (x : ℝ) : (sin x).im = 0 := by rw [← ofReal_sin_ofReal_re, ofReal_im]

theorem sin_ofReal_re (x : ℝ) : (sin x).re = Real.sin x :=
  rfl

theorem cos_conj : cos (conj x) = conj (cos x) := by
  rw [← cosh_mul_I, ← conj_neg_I, ← RingHom.map_mul, ← cosh_mul_I, cosh_conj, mul_neg, cosh_neg]

@[simp]
theorem ofReal_cos_ofReal_re (x : ℝ) : ((cos x).re : ℂ) = cos x :=
  conj_eq_iff_re.1 <| by rw [← cos_conj, conj_ofReal]

@[simp, norm_cast]
theorem ofReal_cos (x : ℝ) : (Real.cos x : ℂ) = cos x :=
  ofReal_cos_ofReal_re _

@[simp]
theorem cos_ofReal_im (x : ℝ) : (cos x).im = 0 := by rw [← ofReal_cos_ofReal_re, ofReal_im]

theorem cos_ofReal_re (x : ℝ) : (cos x).re = Real.cos x :=
  rfl

@[simp]
theorem tan_zero : tan 0 = 0 := by simp [tan]

theorem tan_eq_sin_div_cos : tan x = sin x / cos x :=
  rfl

theorem cot_eq_cos_div_sin : cot x = cos x / sin x :=
  rfl

theorem tan_mul_cos {x : ℂ} (hx : cos x ≠ 0) : tan x * cos x = sin x := by
  rw [tan_eq_sin_div_cos, div_mul_cancel₀ _ hx]

@[simp]
theorem tan_neg : tan (-x) = -tan x := by simp [tan, neg_div]

theorem tan_conj : tan (conj x) = conj (tan x) := by rw [tan, sin_conj, cos_conj, ← map_div₀, tan]

theorem cot_conj : cot (conj x) = conj (cot x) := by rw [cot, sin_conj, cos_conj, ← map_div₀, cot]

@[simp]
theorem ofReal_tan_ofReal_re (x : ℝ) : ((tan x).re : ℂ) = tan x :=
  conj_eq_iff_re.1 <| by rw [← tan_conj, conj_ofReal]

@[simp]
theorem ofReal_cot_ofReal_re (x : ℝ) : ((cot x).re : ℂ) = cot x :=
  conj_eq_iff_re.1 <| by rw [← cot_conj, conj_ofReal]

@[simp, norm_cast]
theorem ofReal_tan (x : ℝ) : (Real.tan x : ℂ) = tan x :=
  ofReal_tan_ofReal_re _

@[simp, norm_cast]
theorem ofReal_cot (x : ℝ) : (Real.cot x : ℂ) = cot x :=
  ofReal_cot_ofReal_re _

@[simp]
theorem tan_ofReal_im (x : ℝ) : (tan x).im = 0 := by rw [← ofReal_tan_ofReal_re, ofReal_im]

theorem tan_ofReal_re (x : ℝ) : (tan x).re = Real.tan x :=
  rfl

theorem cos_add_sin_I : cos x + sin x * I = exp (x * I) := by
  rw [← cosh_add_sinh, sinh_mul_I, cosh_mul_I]

theorem cos_sub_sin_I : cos x - sin x * I = exp (-x * I) := by
  rw [neg_mul, ← cosh_sub_sinh, sinh_mul_I, cosh_mul_I]

@[simp]
theorem sin_sq_add_cos_sq : sin x ^ 2 + cos x ^ 2 = 1 :=
  Eq.trans (by rw [cosh_mul_I, sinh_mul_I, mul_pow, I_sq, mul_neg_one, sub_neg_eq_add, add_comm])
    (cosh_sq_sub_sinh_sq (x * I))

@[simp]
theorem cos_sq_add_sin_sq : cos x ^ 2 + sin x ^ 2 = 1 := by rw [add_comm, sin_sq_add_cos_sq]

theorem cos_two_mul' : cos (2 * x) = cos x ^ 2 - sin x ^ 2 := by rw [two_mul, cos_add, ← sq, ← sq]

theorem cos_two_mul : cos (2 * x) = 2 * cos x ^ 2 - 1 := by
  rw [cos_two_mul', eq_sub_iff_add_eq.2 (sin_sq_add_cos_sq x), ← sub_add, sub_add_eq_add_sub,
    two_mul]

theorem sin_two_mul : sin (2 * x) = 2 * sin x * cos x := by
  rw [two_mul, sin_add, two_mul, add_mul, mul_comm]

theorem cos_sq : cos x ^ 2 = 1 / 2 + cos (2 * x) / 2 := by
  simp [cos_two_mul, div_add_div_same, mul_div_cancel_left₀, two_ne_zero, -one_div]

theorem cos_sq' : cos x ^ 2 = 1 - sin x ^ 2 := by rw [← sin_sq_add_cos_sq x, add_sub_cancel_left]

theorem sin_sq : sin x ^ 2 = 1 - cos x ^ 2 := by rw [← sin_sq_add_cos_sq x, add_sub_cancel_right]

theorem inv_one_add_tan_sq {x : ℂ} (hx : cos x ≠ 0) : (1 + tan x ^ 2)⁻¹ = cos x ^ 2 := by
  rw [tan_eq_sin_div_cos, div_pow]
  field_simp

theorem tan_sq_div_one_add_tan_sq {x : ℂ} (hx : cos x ≠ 0) :
    tan x ^ 2 / (1 + tan x ^ 2) = sin x ^ 2 := by
  simp only [← tan_mul_cos hx, mul_pow, ← inv_one_add_tan_sq hx, div_eq_mul_inv, one_mul]

theorem cos_three_mul : cos (3 * x) = 4 * cos x ^ 3 - 3 * cos x := by
  have h1 : x + 2 * x = 3 * x := by ring
  rw [← h1, cos_add x (2 * x)]
  simp only [cos_two_mul, sin_two_mul, mul_add, mul_sub, mul_one, sq]
  have h2 : 4 * cos x ^ 3 = 2 * cos x * cos x * cos x + 2 * cos x * cos x ^ 2 := by ring
  rw [h2, cos_sq']
  ring

theorem sin_three_mul : sin (3 * x) = 3 * sin x - 4 * sin x ^ 3 := by
  have h1 : x + 2 * x = 3 * x := by ring
  rw [← h1, sin_add x (2 * x)]
  simp only [cos_two_mul, sin_two_mul, cos_sq']
  have h2 : cos x * (2 * sin x * cos x) = 2 * sin x * cos x ^ 2 := by ring
  rw [h2, cos_sq']
  ring

theorem exp_mul_I : exp (x * I) = cos x + sin x * I :=
  (cos_add_sin_I _).symm

theorem exp_add_mul_I : exp (x + y * I) = exp x * (cos y + sin y * I) := by rw [exp_add, exp_mul_I]

theorem exp_eq_exp_re_mul_sin_add_cos : exp x = exp x.re * (cos x.im + sin x.im * I) := by
  rw [← exp_add_mul_I, re_add_im]

theorem exp_re : (exp x).re = Real.exp x.re * Real.cos x.im := by
  rw [exp_eq_exp_re_mul_sin_add_cos]
  simp [exp_ofReal_re, cos_ofReal_re]

theorem exp_im : (exp x).im = Real.exp x.re * Real.sin x.im := by
  rw [exp_eq_exp_re_mul_sin_add_cos]
  simp [exp_ofReal_re, sin_ofReal_re]

@[simp]
theorem exp_ofReal_mul_I_re (x : ℝ) : (exp (x * I)).re = Real.cos x := by
  simp [exp_mul_I, cos_ofReal_re]

@[simp]
theorem exp_ofReal_mul_I_im (x : ℝ) : (exp (x * I)).im = Real.sin x := by
  simp [exp_mul_I, sin_ofReal_re]

/-- **De Moivre's formula** -/
theorem cos_add_sin_mul_I_pow (n : ℕ) (z : ℂ) :
    (cos z + sin z * I) ^ n = cos (↑n * z) + sin (↑n * z) * I := by
  rw [← exp_mul_I, ← exp_mul_I, ← exp_nat_mul, mul_assoc]

end Complex

namespace Real

open Complex

variable (x y : ℝ)

@[simp]
theorem sin_zero : sin 0 = 0 := by simp [sin]

@[simp]
theorem sin_neg : sin (-x) = -sin x := by simp [sin, exp_neg, (neg_div _ _).symm, add_mul]

nonrec theorem sin_add : sin (x + y) = sin x * cos y + cos x * sin y :=
  ofReal_injective <| by simp [sin_add]

@[simp]
theorem cos_zero : cos 0 = 1 := by simp [cos]

@[simp]
theorem cos_neg : cos (-x) = cos x := by simp [cos, exp_neg]

@[simp]
theorem cos_abs : cos |x| = cos x := by
  cases le_total x 0 <;> simp only [*, abs_of_nonneg, abs_of_nonpos, cos_neg]

nonrec theorem cos_add : cos (x + y) = cos x * cos y - sin x * sin y :=
  ofReal_injective <| by simp [cos_add]

theorem sin_sub : sin (x - y) = sin x * cos y - cos x * sin y := by
  simp [sub_eq_add_neg, sin_add, sin_neg, cos_neg]

theorem cos_sub : cos (x - y) = cos x * cos y + sin x * sin y := by
  simp [sub_eq_add_neg, cos_add, sin_neg, cos_neg]

nonrec theorem sin_sub_sin : sin x - sin y = 2 * sin ((x - y) / 2) * cos ((x + y) / 2) :=
  ofReal_injective <| by simp [sin_sub_sin]

nonrec theorem cos_sub_cos : cos x - cos y = -2 * sin ((x + y) / 2) * sin ((x - y) / 2) :=
  ofReal_injective <| by simp [cos_sub_cos]

nonrec theorem cos_add_cos : cos x + cos y = 2 * cos ((x + y) / 2) * cos ((x - y) / 2) :=
  ofReal_injective <| by simp [cos_add_cos]

theorem two_mul_sin_mul_sin (x y : ℝ) : 2 * sin x * sin y = cos (x - y) - cos (x + y) := by
  simp [cos_add, cos_sub]
  ring

theorem two_mul_cos_mul_cos (x y : ℝ) : 2 * cos x * cos y = cos (x - y) + cos (x + y) := by
  simp [cos_add, cos_sub]
  ring

theorem two_mul_sin_mul_cos (x y : ℝ) : 2 * sin x * cos y = sin (x - y) + sin (x + y) := by
  simp [sin_add, sin_sub]
  ring

nonrec theorem tan_eq_sin_div_cos : tan x = sin x / cos x :=
  ofReal_injective <| by simp only [ofReal_tan, tan_eq_sin_div_cos, ofReal_div, ofReal_sin,
    ofReal_cos]

nonrec theorem cot_eq_cos_div_sin : cot x = cos x / sin x :=
  ofReal_injective <| by simp [cot_eq_cos_div_sin]

theorem tan_mul_cos {x : ℝ} (hx : cos x ≠ 0) : tan x * cos x = sin x := by
  rw [tan_eq_sin_div_cos, div_mul_cancel₀ _ hx]

@[simp]
theorem tan_zero : tan 0 = 0 := by simp [tan]

@[simp]
theorem tan_neg : tan (-x) = -tan x := by simp [tan, neg_div]

@[simp]
nonrec theorem sin_sq_add_cos_sq : sin x ^ 2 + cos x ^ 2 = 1 :=
  ofReal_injective (by simp [sin_sq_add_cos_sq])

@[simp]
theorem cos_sq_add_sin_sq : cos x ^ 2 + sin x ^ 2 = 1 := by rw [add_comm, sin_sq_add_cos_sq]

theorem sin_sq_le_one : sin x ^ 2 ≤ 1 := by
  rw [← sin_sq_add_cos_sq x]; exact le_add_of_nonneg_right (sq_nonneg _)

theorem cos_sq_le_one : cos x ^ 2 ≤ 1 := by
  rw [← sin_sq_add_cos_sq x]; exact le_add_of_nonneg_left (sq_nonneg _)

theorem abs_sin_le_one : |sin x| ≤ 1 :=
  abs_le_one_iff_mul_self_le_one.2 <| by simp only [← sq, sin_sq_le_one]

theorem abs_cos_le_one : |cos x| ≤ 1 :=
  abs_le_one_iff_mul_self_le_one.2 <| by simp only [← sq, cos_sq_le_one]

theorem sin_le_one : sin x ≤ 1 :=
  (abs_le.1 (abs_sin_le_one _)).2

theorem cos_le_one : cos x ≤ 1 :=
  (abs_le.1 (abs_cos_le_one _)).2

theorem neg_one_le_sin : -1 ≤ sin x :=
  (abs_le.1 (abs_sin_le_one _)).1

theorem neg_one_le_cos : -1 ≤ cos x :=
  (abs_le.1 (abs_cos_le_one _)).1

nonrec theorem cos_two_mul : cos (2 * x) = 2 * cos x ^ 2 - 1 :=
  ofReal_injective <| by simp [cos_two_mul]

nonrec theorem cos_two_mul' : cos (2 * x) = cos x ^ 2 - sin x ^ 2 :=
  ofReal_injective <| by simp [cos_two_mul']

nonrec theorem sin_two_mul : sin (2 * x) = 2 * sin x * cos x :=
  ofReal_injective <| by simp [sin_two_mul]

nonrec theorem cos_sq : cos x ^ 2 = 1 / 2 + cos (2 * x) / 2 :=
  ofReal_injective <| by simp [cos_sq]

theorem cos_sq' : cos x ^ 2 = 1 - sin x ^ 2 := by rw [← sin_sq_add_cos_sq x, add_sub_cancel_left]

theorem sin_sq : sin x ^ 2 = 1 - cos x ^ 2 :=
  eq_sub_iff_add_eq.2 <| sin_sq_add_cos_sq _

lemma sin_sq_eq_half_sub : sin x ^ 2 = 1 / 2 - cos (2 * x) / 2 := by
  rw [sin_sq, cos_sq, ← sub_sub, sub_half]

theorem abs_sin_eq_sqrt_one_sub_cos_sq (x : ℝ) : |sin x| = √(1 - cos x ^ 2) := by
  rw [← sin_sq, sqrt_sq_eq_abs]

theorem abs_cos_eq_sqrt_one_sub_sin_sq (x : ℝ) : |cos x| = √(1 - sin x ^ 2) := by
  rw [← cos_sq', sqrt_sq_eq_abs]

theorem inv_one_add_tan_sq {x : ℝ} (hx : cos x ≠ 0) : (1 + tan x ^ 2)⁻¹ = cos x ^ 2 :=
  have : Complex.cos x ≠ 0 := mt (congr_arg re) hx
  ofReal_inj.1 <| by simpa using Complex.inv_one_add_tan_sq this

theorem tan_sq_div_one_add_tan_sq {x : ℝ} (hx : cos x ≠ 0) :
    tan x ^ 2 / (1 + tan x ^ 2) = sin x ^ 2 := by
  simp only [← tan_mul_cos hx, mul_pow, ← inv_one_add_tan_sq hx, div_eq_mul_inv, one_mul]

theorem inv_sqrt_one_add_tan_sq {x : ℝ} (hx : 0 < cos x) : (√(1 + tan x ^ 2))⁻¹ = cos x := by
  rw [← sqrt_sq hx.le, ← sqrt_inv, inv_one_add_tan_sq hx.ne']

theorem tan_div_sqrt_one_add_tan_sq {x : ℝ} (hx : 0 < cos x) :
    tan x / √(1 + tan x ^ 2) = sin x := by
  rw [← tan_mul_cos hx.ne', ← inv_sqrt_one_add_tan_sq hx, div_eq_mul_inv]

nonrec theorem cos_three_mul : cos (3 * x) = 4 * cos x ^ 3 - 3 * cos x := by
  rw [← ofReal_inj]; simp [cos_three_mul]

nonrec theorem sin_three_mul : sin (3 * x) = 3 * sin x - 4 * sin x ^ 3 := by
  rw [← ofReal_inj]; simp [sin_three_mul]

/-- The definition of `sinh` in terms of `exp`. -/
nonrec theorem sinh_eq (x : ℝ) : sinh x = (exp x - exp (-x)) / 2 :=
  ofReal_injective <| by simp [Complex.sinh]

@[simp]
theorem sinh_zero : sinh 0 = 0 := by simp [sinh]

@[simp]
theorem sinh_neg : sinh (-x) = -sinh x := by simp [sinh, exp_neg, (neg_div _ _).symm, add_mul]

nonrec theorem sinh_add : sinh (x + y) = sinh x * cosh y + cosh x * sinh y := by
  rw [← ofReal_inj]; simp [sinh_add]

/-- The definition of `cosh` in terms of `exp`. -/
theorem cosh_eq (x : ℝ) : cosh x = (exp x + exp (-x)) / 2 :=
  eq_div_of_mul_eq two_ne_zero <| by
    rw [cosh, exp, exp, Complex.ofReal_neg, Complex.cosh, mul_two, ← Complex.add_re, ← mul_two,
      div_mul_cancel₀ _ (two_ne_zero' ℂ), Complex.add_re]

@[simp]
theorem cosh_zero : cosh 0 = 1 := by simp [cosh]

@[simp]
theorem cosh_neg : cosh (-x) = cosh x :=
  ofReal_inj.1 <| by simp

@[simp]
theorem cosh_abs : cosh |x| = cosh x := by
  cases le_total x 0 <;> simp [*, abs_of_nonneg, abs_of_nonpos]

nonrec theorem cosh_add : cosh (x + y) = cosh x * cosh y + sinh x * sinh y := by
  rw [← ofReal_inj]; simp [cosh_add]

theorem sinh_sub : sinh (x - y) = sinh x * cosh y - cosh x * sinh y := by
  simp [sub_eq_add_neg, sinh_add, sinh_neg, cosh_neg]

theorem cosh_sub : cosh (x - y) = cosh x * cosh y - sinh x * sinh y := by
  simp [sub_eq_add_neg, cosh_add, sinh_neg, cosh_neg]

nonrec theorem tanh_eq_sinh_div_cosh : tanh x = sinh x / cosh x :=
  ofReal_inj.1 <| by simp [tanh_eq_sinh_div_cosh]

@[simp]
theorem tanh_zero : tanh 0 = 0 := by simp [tanh]

@[simp]
theorem tanh_neg : tanh (-x) = -tanh x := by simp [tanh, neg_div]

@[simp]
theorem cosh_add_sinh : cosh x + sinh x = exp x := by rw [← ofReal_inj]; simp

@[simp]
theorem sinh_add_cosh : sinh x + cosh x = exp x := by rw [add_comm, cosh_add_sinh]

@[simp]
theorem exp_sub_cosh : exp x - cosh x = sinh x :=
  sub_eq_iff_eq_add.2 (sinh_add_cosh x).symm

@[simp]
theorem exp_sub_sinh : exp x - sinh x = cosh x :=
  sub_eq_iff_eq_add.2 (cosh_add_sinh x).symm

@[simp]
theorem cosh_sub_sinh : cosh x - sinh x = exp (-x) := by
  rw [← ofReal_inj]
  simp

@[simp]
theorem sinh_sub_cosh : sinh x - cosh x = -exp (-x) := by rw [← neg_sub, cosh_sub_sinh]

@[simp]
theorem cosh_sq_sub_sinh_sq (x : ℝ) : cosh x ^ 2 - sinh x ^ 2 = 1 := by rw [← ofReal_inj]; simp

nonrec theorem cosh_sq : cosh x ^ 2 = sinh x ^ 2 + 1 := by rw [← ofReal_inj]; simp [cosh_sq]

theorem cosh_sq' : cosh x ^ 2 = 1 + sinh x ^ 2 :=
  (cosh_sq x).trans (add_comm _ _)

nonrec theorem sinh_sq : sinh x ^ 2 = cosh x ^ 2 - 1 := by rw [← ofReal_inj]; simp [sinh_sq]

nonrec theorem cosh_two_mul : cosh (2 * x) = cosh x ^ 2 + sinh x ^ 2 := by
  rw [← ofReal_inj]; simp [cosh_two_mul]

nonrec theorem sinh_two_mul : sinh (2 * x) = 2 * sinh x * cosh x := by
  rw [← ofReal_inj]; simp [sinh_two_mul]

nonrec theorem cosh_three_mul : cosh (3 * x) = 4 * cosh x ^ 3 - 3 * cosh x := by
  rw [← ofReal_inj]; simp [cosh_three_mul]

nonrec theorem sinh_three_mul : sinh (3 * x) = 4 * sinh x ^ 3 + 3 * sinh x := by
  rw [← ofReal_inj]; simp [sinh_three_mul]

open IsAbsoluteValue Nat

private theorem add_one_lt_exp_of_pos {x : ℝ} (hx : 0 < x) : x + 1 < exp x :=
  (by nlinarith : x + 1 < 1 + x + x ^ 2 / 2).trans_le (quadratic_le_exp_of_nonneg hx.le)

private theorem add_one_le_exp_of_nonneg {x : ℝ} (hx : 0 ≤ x) : x + 1 ≤ exp x := by
  rcases eq_or_lt_of_le hx with (rfl | h)
  · simp
  exact (add_one_lt_exp_of_pos h).le

/-- `Real.cosh` is always positive -/
theorem cosh_pos (x : ℝ) : 0 < Real.cosh x :=
  (cosh_eq x).symm ▸ half_pos (add_pos (exp_pos x) (exp_pos (-x)))

theorem sinh_lt_cosh : sinh x < cosh x :=
  lt_of_pow_lt_pow_left₀ 2 (cosh_pos _).le <| (cosh_sq x).symm ▸ lt_add_one _

end Real

namespace Real

open Complex Finset

theorem cos_bound {x : ℝ} (hx : |x| ≤ 1) : |cos x - (1 - x ^ 2 / 2)| ≤ |x| ^ 4 * (5 / 96) :=
  calc
    |cos x - (1 - x ^ 2 / 2)| = ‖Complex.cos x - (1 - (x : ℂ) ^ 2 / 2)‖ := by
      rw [← Real.norm_eq_abs, ← norm_real]; simp
    _ = ‖(Complex.exp (x * I) + Complex.exp (-x * I) - (2 - (x : ℂ) ^ 2)) / 2‖ := by
      simp [Complex.cos, sub_div, add_div, neg_div, div_self (two_ne_zero' ℂ)]
    _ = ‖((Complex.exp (x * I) - ∑ m ∈ range 4, (x * I) ^ m / m.factorial) +
              (Complex.exp (-x * I) - ∑ m ∈ range 4, (-x * I) ^ m / m.factorial)) / 2‖ :=
      (congr_arg (‖·‖ : ℂ → ℝ)
        (congr_arg (fun x : ℂ => x / 2) (by
          simp only [neg_mul, pow_succ, pow_zero, sum_range_succ, range_zero, sum_empty,
          Nat.factorial, Nat.cast_succ, zero_add, mul_one, Nat.mul_one, mul_neg, neg_neg]
          apply Complex.ext <;> simp [div_eq_mul_inv, normSq] <;> ring_nf)))
    _ ≤ ‖(Complex.exp (x * I) - ∑ m ∈ range 4, (x * I) ^ m / m.factorial) / 2‖ +
          ‖(Complex.exp (-x * I) - ∑ m ∈ range 4, (-x * I) ^ m / m.factorial) / 2‖ := by
      rw [add_div]; exact norm_add_le _ _
    _ = ‖Complex.exp (x * I) - ∑ m ∈ range 4, (x * I) ^ m / m.factorial‖ / 2 +
          ‖Complex.exp (-x * I) - ∑ m ∈ range 4, (-x * I) ^ m / m.factorial‖ / 2 := by
      simp [map_div₀]
    _ ≤ ‖x * I‖ ^ 4 * (Nat.succ 4 * ((Nat.factorial 4) * (4 : ℕ) : ℝ)⁻¹) / 2 +
          ‖-x * I‖ ^ 4 * (Nat.succ 4 * ((Nat.factorial 4) * (4 : ℕ) : ℝ)⁻¹) / 2 := by
      gcongr
      · exact Complex.exp_bound (by simpa) (by decide)
      · exact Complex.exp_bound (by simpa) (by decide)
    _ ≤ |x| ^ 4 * (5 / 96) := by norm_num [Nat.factorial]

theorem sin_bound {x : ℝ} (hx : |x| ≤ 1) : |sin x - (x - x ^ 3 / 6)| ≤ |x| ^ 4 * (5 / 96) :=
  calc
    |sin x - (x - x ^ 3 / 6)| = ‖Complex.sin x - (x - x ^ 3 / 6 : ℝ)‖ := by
      rw [← Real.norm_eq_abs, ← norm_real]; simp
    _ = ‖((Complex.exp (-x * I) - Complex.exp (x * I)) * I -
          (2 * x - x ^ 3 / 3 : ℝ)) / 2‖ := by
      simp [Complex.sin, sub_div, add_div, neg_div, mul_div_cancel_left₀ _ (two_ne_zero' ℂ),
        div_div, show (3 : ℂ) * 2 = 6 by norm_num]
    _ = ‖((Complex.exp (-x * I) - ∑ m ∈ range 4, (-x * I) ^ m / m.factorial) -
                (Complex.exp (x * I) - ∑ m ∈ range 4, (x * I) ^ m / m.factorial)) * I / 2‖ :=
      (congr_arg (‖·‖ : ℂ → ℝ)
        (congr_arg (fun x : ℂ => x / 2)
          (by
            simp only [neg_mul, pow_succ, pow_zero, ofReal_sub, ofReal_mul, ofReal_ofNat,
              ofReal_div, sum_range_succ, range_zero, sum_empty, Nat.factorial, Nat.cast_succ,
              zero_add, mul_neg, mul_one, neg_neg, Nat.mul_one]
            apply Complex.ext <;> simp [div_eq_mul_inv, normSq]; ring)))
    _ ≤ ‖(Complex.exp (-x * I) - ∑ m ∈ range 4, (-x * I) ^ m / m.factorial) * I / 2‖ +
          ‖-((Complex.exp (x * I) - ∑ m ∈ range 4, (x * I) ^ m / m.factorial) * I) / 2‖ := by
      rw [sub_mul, sub_eq_add_neg, add_div]; exact norm_add_le _ _
    _ = ‖Complex.exp (x * I) - ∑ m ∈ range 4, (x * I) ^ m / m.factorial‖ / 2 +
          ‖Complex.exp (-x * I) - ∑ m ∈ range 4, (-x * I) ^ m / m.factorial‖ / 2 := by
      simp [add_comm, map_div₀]
    _ ≤ ‖x * I‖ ^ 4 * (Nat.succ 4 * (Nat.factorial 4 * (4 : ℕ) : ℝ)⁻¹) / 2 +
          ‖-x * I‖ ^ 4 * (Nat.succ 4 * (Nat.factorial 4 * (4 : ℕ) : ℝ)⁻¹) / 2 := by
      gcongr
      · exact Complex.exp_bound (by simpa) (by decide)
      · exact Complex.exp_bound (by simpa) (by decide)
    _ ≤ |x| ^ 4 * (5 / 96) := by norm_num [Nat.factorial]

theorem cos_pos_of_le_one {x : ℝ} (hx : |x| ≤ 1) : 0 < cos x :=
  calc 0 < 1 - x ^ 2 / 2 - |x| ^ 4 * (5 / 96) :=
      sub_pos.2 <|
        lt_sub_iff_add_lt.2
          (calc
            |x| ^ 4 * (5 / 96) + x ^ 2 / 2 ≤ 1 * (5 / 96) + 1 / 2 := by
                  gcongr
                  · exact pow_le_one₀ (abs_nonneg _) hx
                  · rw [sq, ← abs_mul_self, abs_mul]
                    exact mul_le_one₀ hx (abs_nonneg _) hx
            _ < 1 := by norm_num)
    _ ≤ cos x := sub_le_comm.1 (abs_sub_le_iff.1 (cos_bound hx)).2

theorem sin_pos_of_pos_of_le_one {x : ℝ} (hx0 : 0 < x) (hx : x ≤ 1) : 0 < sin x :=
  calc 0 < x - x ^ 3 / 6 - |x| ^ 4 * (5 / 96) :=
      sub_pos.2 <| lt_sub_iff_add_lt.2
          (calc
            |x| ^ 4 * (5 / 96) + x ^ 3 / 6 ≤ x * (5 / 96) + x / 6 := by
                gcongr
                · calc
                    |x| ^ 4 ≤ |x| ^ 1 :=
                      pow_le_pow_of_le_one (abs_nonneg _)
                        (by rwa [abs_of_nonneg (le_of_lt hx0)]) (by decide)
                    _ = x := by simp [abs_of_nonneg (le_of_lt hx0)]
                · calc
                    x ^ 3 ≤ x ^ 1 := pow_le_pow_of_le_one (le_of_lt hx0) hx (by decide)
                    _ = x := pow_one _
            _ < x := by linarith)
    _ ≤ sin x :=
      sub_le_comm.1 (abs_sub_le_iff.1 (sin_bound (by rwa [abs_of_nonneg (le_of_lt hx0)]))).2

theorem sin_pos_of_pos_of_le_two {x : ℝ} (hx0 : 0 < x) (hx : x ≤ 2) : 0 < sin x :=
  have : x / 2 ≤ 1 := (div_le_iff₀ (by norm_num)).mpr (by simpa)
  calc
    0 < 2 * sin (x / 2) * cos (x / 2) :=
      mul_pos (mul_pos (by norm_num) (sin_pos_of_pos_of_le_one (half_pos hx0) this))
        (cos_pos_of_le_one (by rwa [abs_of_nonneg (le_of_lt (half_pos hx0))]))
    _ = sin x := by rw [← sin_two_mul, two_mul, add_halves]

theorem cos_one_le : cos 1 ≤ 5 / 9 :=
  calc
    cos 1 ≤ |(1 : ℝ)| ^ 4 * (5 / 96) + (1 - 1 ^ 2 / 2) :=
      sub_le_iff_le_add.1 (abs_sub_le_iff.1 (cos_bound (by simp))).1
    _ ≤ 5 / 9 := by norm_num

theorem cos_one_pos : 0 < cos 1 :=
  cos_pos_of_le_one (le_of_eq abs_one)

theorem cos_two_neg : cos 2 < 0 :=
  calc cos 2 = cos (2 * 1) := congr_arg cos (mul_one _).symm
    _ = _ := Real.cos_two_mul 1
    _ ≤ 2 * (5 / 9) ^ 2 - 1 := by
      gcongr
      · exact cos_one_pos.le
      · apply cos_one_le
    _ < 0 := by norm_num

end Real

namespace Mathlib.Meta.Positivity
open Lean.Meta Qq

/-- Extension for the `positivity` tactic: `Real.cosh` is always positive. -/
@[positivity Real.cosh _]
def evalCosh : PositivityExt where eval {u α} _ _ e := do
  match u, α, e with
  | 0, ~q(ℝ), ~q(Real.cosh $a) =>
    assertInstancesCommute
    return .positive q(Real.cosh_pos $a)
  | _, _, _ => throwError "not Real.cosh"

example (x : ℝ) : 0 < x.cosh := by positivity

end Mathlib.Meta.Positivity

namespace Complex

@[simp]
theorem norm_cos_add_sin_mul_I (x : ℝ) : ‖cos x + sin x * I‖ = 1 := by
  have := Real.sin_sq_add_cos_sq x
  simp_all [add_comm, norm_def, normSq, sq, sin_ofReal_re, cos_ofReal_re, mul_re]

@[simp]
theorem norm_exp_ofReal_mul_I (x : ℝ) : ‖exp (x * I)‖ = 1 := by
  rw [exp_mul_I, norm_cos_add_sin_mul_I]

theorem norm_exp (z : ℂ) : ‖exp z‖ = Real.exp z.re := by
  rw [exp_eq_exp_re_mul_sin_add_cos, Complex.norm_mul, norm_exp_ofReal, norm_cos_add_sin_mul_I,
    mul_one]

theorem norm_exp_eq_iff_re_eq {x y : ℂ} : ‖exp x‖ = ‖exp y‖ ↔ x.re = y.re := by
  rw [norm_exp, norm_exp, Real.exp_eq_exp]

@[deprecated (since := "2025-02-16")] alias abs_cos_add_sin_mul_I := norm_cos_add_sin_mul_I
@[deprecated (since := "2025-02-16")] alias abs_exp_ofReal_mul_I := norm_exp_ofReal_mul_I
@[deprecated (since := "2025-02-16")] alias abs_exp := norm_exp
@[deprecated (since := "2025-02-16")] alias abs_exp_eq_iff_re_eq := norm_exp_eq_iff_re_eq

end Complex
