/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Sébastien Gouëzel,
  Rémy Degenne, David Loeffler
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Qq

#align_import analysis.special_functions.pow.real from "leanprover-community/mathlib"@"4fa54b337f7d52805480306db1b1439c741848c8"


/-! # Power function on `ℝ`

We construct the power functions `x ^ y`, where `x` and `y` are real numbers.
-/


noncomputable section

open Classical Real BigOperators ComplexConjugate

open Finset Set

/-
## Definitions
-/
namespace Real

/-- The real power function `x ^ y`, defined as the real part of the complex power function.
For `x > 0`, it is equal to `exp (y log x)`. For `x = 0`, one sets `0 ^ 0=1` and `0 ^ y=0` for
`y ≠ 0`. For `x < 0`, the definition is somewhat arbitrary as it depends on the choice of a complex
determination of the logarithm. With our conventions, it is equal to `exp (y log x) cos (π y)`. -/
noncomputable def rpow (x y : ℝ) :=
  ((x : ℂ) ^ (y : ℂ)).re
#align real.rpow Real.rpow

noncomputable instance : Pow ℝ ℝ := ⟨rpow⟩

@[simp]
theorem rpow_eq_pow (x y : ℝ) : rpow x y = x ^ y := rfl
#align real.rpow_eq_pow Real.rpow_eq_pow

theorem rpow_def (x y : ℝ) : x ^ y = ((x : ℂ) ^ (y : ℂ)).re := rfl
#align real.rpow_def Real.rpow_def

theorem rpow_def_of_nonneg {x : ℝ} (hx : 0 ≤ x) (y : ℝ) :
    x ^ y = if x = 0 then if y = 0 then 1 else 0 else exp (log x * y) := by
  simp only [rpow_def, Complex.cpow_def]; split_ifs <;>
  simp_all [(Complex.ofReal_log hx).symm, -Complex.ofReal_mul, -IsROrC.ofReal_mul,
      (Complex.ofReal_mul _ _).symm, Complex.exp_ofReal_re, Complex.ofReal_eq_zero]
#align real.rpow_def_of_nonneg Real.rpow_def_of_nonneg

theorem rpow_def_of_pos {x : ℝ} (hx : 0 < x) (y : ℝ) : x ^ y = exp (log x * y) := by
  rw [rpow_def_of_nonneg (le_of_lt hx), if_neg (ne_of_gt hx)]
#align real.rpow_def_of_pos Real.rpow_def_of_pos

theorem exp_mul (x y : ℝ) : exp (x * y) = exp x ^ y := by rw [rpow_def_of_pos (exp_pos _), log_exp]
#align real.exp_mul Real.exp_mul

@[simp]
theorem exp_one_rpow (x : ℝ) : exp 1 ^ x = exp x := by rw [← exp_mul, one_mul]
#align real.exp_one_rpow Real.exp_one_rpow

theorem rpow_eq_zero_iff_of_nonneg {x y : ℝ} (hx : 0 ≤ x) : x ^ y = 0 ↔ x = 0 ∧ y ≠ 0 := by
  simp only [rpow_def_of_nonneg hx]
  split_ifs <;> simp [*, exp_ne_zero]
#align real.rpow_eq_zero_iff_of_nonneg Real.rpow_eq_zero_iff_of_nonneg

open Real

theorem rpow_def_of_neg {x : ℝ} (hx : x < 0) (y : ℝ) : x ^ y = exp (log x * y) * cos (y * π) := by
  rw [rpow_def, Complex.cpow_def, if_neg]
  have : Complex.log x * y = ↑(log (-x) * y) + ↑(y * π) * Complex.I := by
    simp only [Complex.log, abs_of_neg hx, Complex.arg_ofReal_of_neg hx, Complex.abs_ofReal,
      Complex.ofReal_mul]
    ring
  · rw [this, Complex.exp_add_mul_I, ← Complex.ofReal_exp, ← Complex.ofReal_cos, ←
      Complex.ofReal_sin, mul_add, ← Complex.ofReal_mul, ← mul_assoc, ← Complex.ofReal_mul,
      Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
      Real.log_neg_eq_log]
    ring
  · rw [Complex.ofReal_eq_zero]
    exact ne_of_lt hx
#align real.rpow_def_of_neg Real.rpow_def_of_neg

theorem rpow_def_of_nonpos {x : ℝ} (hx : x ≤ 0) (y : ℝ) :
    x ^ y = if x = 0 then if y = 0 then 1 else 0 else exp (log x * y) * cos (y * π) := by
  split_ifs with h <;> simp [rpow_def, *]; exact rpow_def_of_neg (lt_of_le_of_ne hx h) _
#align real.rpow_def_of_nonpos Real.rpow_def_of_nonpos

theorem rpow_pos_of_pos {x : ℝ} (hx : 0 < x) (y : ℝ) : 0 < x ^ y := by
  rw [rpow_def_of_pos hx]; apply exp_pos
#align real.rpow_pos_of_pos Real.rpow_pos_of_pos

@[simp]
theorem rpow_zero (x : ℝ) : x ^ (0 : ℝ) = 1 := by simp [rpow_def]
#align real.rpow_zero Real.rpow_zero

theorem rpow_zero_pos (x : ℝ) : 0 < x ^ (0 : ℝ) := by simp

@[simp]
theorem zero_rpow {x : ℝ} (h : x ≠ 0) : (0 : ℝ) ^ x = 0 := by simp [rpow_def, *]
#align real.zero_rpow Real.zero_rpow

theorem zero_rpow_eq_iff {x : ℝ} {a : ℝ} : 0 ^ x = a ↔ x ≠ 0 ∧ a = 0 ∨ x = 0 ∧ a = 1 := by
  constructor
  · intro hyp
    simp only [rpow_def, Complex.ofReal_zero] at hyp
    by_cases h : x = 0
    · subst h
      simp only [Complex.one_re, Complex.ofReal_zero, Complex.cpow_zero] at hyp
      exact Or.inr ⟨rfl, hyp.symm⟩
    · rw [Complex.zero_cpow (Complex.ofReal_ne_zero.mpr h)] at hyp
      exact Or.inl ⟨h, hyp.symm⟩
  · rintro (⟨h, rfl⟩ | ⟨rfl, rfl⟩)
    · exact zero_rpow h
    · exact rpow_zero _
#align real.zero_rpow_eq_iff Real.zero_rpow_eq_iff

theorem eq_zero_rpow_iff {x : ℝ} {a : ℝ} : a = 0 ^ x ↔ x ≠ 0 ∧ a = 0 ∨ x = 0 ∧ a = 1 := by
  rw [← zero_rpow_eq_iff, eq_comm]
#align real.eq_zero_rpow_iff Real.eq_zero_rpow_iff

@[simp]
theorem rpow_one (x : ℝ) : x ^ (1 : ℝ) = x := by simp [rpow_def]
#align real.rpow_one Real.rpow_one

@[simp]
theorem one_rpow (x : ℝ) : (1 : ℝ) ^ x = 1 := by simp [rpow_def]
#align real.one_rpow Real.one_rpow

theorem zero_rpow_le_one (x : ℝ) : (0 : ℝ) ^ x ≤ 1 := by
  by_cases h : x = 0 <;> simp [h, zero_le_one]
#align real.zero_rpow_le_one Real.zero_rpow_le_one

theorem zero_rpow_nonneg (x : ℝ) : 0 ≤ (0 : ℝ) ^ x := by
  by_cases h : x = 0 <;> simp [h, zero_le_one]
#align real.zero_rpow_nonneg Real.zero_rpow_nonneg

theorem rpow_nonneg_of_nonneg {x : ℝ} (hx : 0 ≤ x) (y : ℝ) : 0 ≤ x ^ y := by
  rw [rpow_def_of_nonneg hx]; split_ifs <;>
    simp only [zero_le_one, le_refl, le_of_lt (exp_pos _)]
#align real.rpow_nonneg_of_nonneg Real.rpow_nonneg_of_nonneg

theorem abs_rpow_of_nonneg {x y : ℝ} (hx_nonneg : 0 ≤ x) : |x ^ y| = |x| ^ y := by
  have h_rpow_nonneg : 0 ≤ x ^ y := Real.rpow_nonneg_of_nonneg hx_nonneg _
  rw [abs_eq_self.mpr hx_nonneg, abs_eq_self.mpr h_rpow_nonneg]
#align real.abs_rpow_of_nonneg Real.abs_rpow_of_nonneg

theorem abs_rpow_le_abs_rpow (x y : ℝ) : |x ^ y| ≤ |x| ^ y := by
  cases' le_or_lt 0 x with hx hx
  · rw [abs_rpow_of_nonneg hx]
  · rw [abs_of_neg hx, rpow_def_of_neg hx, rpow_def_of_pos (neg_pos.2 hx), log_neg_eq_log, abs_mul,
      abs_of_pos (exp_pos _)]
    exact mul_le_of_le_one_right (exp_pos _).le (abs_cos_le_one _)
#align real.abs_rpow_le_abs_rpow Real.abs_rpow_le_abs_rpow

theorem abs_rpow_le_exp_log_mul (x y : ℝ) : |x ^ y| ≤ exp (log x * y) := by
  refine' (abs_rpow_le_abs_rpow x y).trans _
  by_cases hx : x = 0
  · by_cases hy : y = 0 <;> simp [hx, hy, zero_le_one]
  · rw [rpow_def_of_pos (abs_pos.2 hx), log_abs]
#align real.abs_rpow_le_exp_log_mul Real.abs_rpow_le_exp_log_mul

theorem norm_rpow_of_nonneg {x y : ℝ} (hx_nonneg : 0 ≤ x) : ‖x ^ y‖ = ‖x‖ ^ y := by
  simp_rw [Real.norm_eq_abs]
  exact abs_rpow_of_nonneg hx_nonneg
#align real.norm_rpow_of_nonneg Real.norm_rpow_of_nonneg

variable {x y z : ℝ}

theorem rpow_add (hx : 0 < x) (y z : ℝ) : x ^ (y + z) = x ^ y * x ^ z := by
  simp only [rpow_def_of_pos hx, mul_add, exp_add]
#align real.rpow_add Real.rpow_add

theorem rpow_add' (hx : 0 ≤ x) (h : y + z ≠ 0) : x ^ (y + z) = x ^ y * x ^ z := by
  rcases hx.eq_or_lt with (rfl | pos)
  · rw [zero_rpow h, zero_eq_mul]
    have : y ≠ 0 ∨ z ≠ 0 := not_and_or.1 fun ⟨hy, hz⟩ => h <| hy.symm ▸ hz.symm ▸ zero_add 0
    exact this.imp zero_rpow zero_rpow
  · exact rpow_add pos _ _
#align real.rpow_add' Real.rpow_add'

theorem rpow_add_of_nonneg (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    x ^ (y + z) = x ^ y * x ^ z := by
  rcases hy.eq_or_lt with (rfl | hy)
  · rw [zero_add, rpow_zero, one_mul]
  exact rpow_add' hx (ne_of_gt <| add_pos_of_pos_of_nonneg hy hz)
#align real.rpow_add_of_nonneg Real.rpow_add_of_nonneg

/-- For `0 ≤ x`, the only problematic case in the equality `x ^ y * x ^ z = x ^ (y + z)` is for
`x = 0` and `y + z = 0`, where the right hand side is `1` while the left hand side can vanish.
The inequality is always true, though, and given in this lemma. -/
theorem le_rpow_add {x : ℝ} (hx : 0 ≤ x) (y z : ℝ) : x ^ y * x ^ z ≤ x ^ (y + z) := by
  rcases le_iff_eq_or_lt.1 hx with (H | pos)
  · by_cases h : y + z = 0
    · simp only [H.symm, h, rpow_zero]
      calc
        (0 : ℝ) ^ y * 0 ^ z ≤ 1 * 1 :=
          mul_le_mul (zero_rpow_le_one y) (zero_rpow_le_one z) (zero_rpow_nonneg z) zero_le_one
        _ = 1 := by simp

    · simp [rpow_add', ← H, h]
  · simp [rpow_add pos]
#align real.le_rpow_add Real.le_rpow_add

theorem rpow_sum_of_pos {ι : Type*} {a : ℝ} (ha : 0 < a) (f : ι → ℝ) (s : Finset ι) :
    (a ^ ∑ x in s, f x) = ∏ x in s, a ^ f x :=
  map_sum (⟨⟨fun (x : ℝ) => (a ^ x : ℝ), rpow_zero a⟩, rpow_add ha⟩ : ℝ →+ (Additive ℝ)) f s
#align real.rpow_sum_of_pos Real.rpow_sum_of_pos

theorem rpow_sum_of_nonneg {ι : Type*} {a : ℝ} (ha : 0 ≤ a) {s : Finset ι} {f : ι → ℝ}
    (h : ∀ x ∈ s, 0 ≤ f x) : (a ^ ∑ x in s, f x) = ∏ x in s, a ^ f x := by
  induction' s using Finset.cons_induction with i s hi ihs
  · rw [sum_empty, Finset.prod_empty, rpow_zero]
  · rw [forall_mem_cons] at h
    rw [sum_cons, prod_cons, ← ihs h.2, rpow_add_of_nonneg ha h.1 (sum_nonneg h.2)]
#align real.rpow_sum_of_nonneg Real.rpow_sum_of_nonneg

theorem rpow_neg {x : ℝ} (hx : 0 ≤ x) (y : ℝ) : x ^ (-y) = (x ^ y)⁻¹ := by
  simp only [rpow_def_of_nonneg hx]; split_ifs <;> simp_all [exp_neg]
#align real.rpow_neg Real.rpow_neg

theorem rpow_sub {x : ℝ} (hx : 0 < x) (y z : ℝ) : x ^ (y - z) = x ^ y / x ^ z := by
  simp only [sub_eq_add_neg, rpow_add hx, rpow_neg (le_of_lt hx), div_eq_mul_inv]
#align real.rpow_sub Real.rpow_sub

theorem rpow_sub' {x : ℝ} (hx : 0 ≤ x) {y z : ℝ} (h : y - z ≠ 0) : x ^ (y - z) = x ^ y / x ^ z := by
  simp only [sub_eq_add_neg] at h ⊢
  simp only [rpow_add' hx h, rpow_neg hx, div_eq_mul_inv]
#align real.rpow_sub' Real.rpow_sub'

end Real

/-!
## Comparing real and complex powers
-/


namespace Complex

theorem ofReal_cpow {x : ℝ} (hx : 0 ≤ x) (y : ℝ) : ((x ^ y : ℝ) : ℂ) = (x : ℂ) ^ (y : ℂ) := by
  simp only [Real.rpow_def_of_nonneg hx, Complex.cpow_def, ofReal_eq_zero]; split_ifs <;>
    simp [Complex.ofReal_log hx]
#align complex.of_real_cpow Complex.ofReal_cpow

theorem ofReal_cpow_of_nonpos {x : ℝ} (hx : x ≤ 0) (y : ℂ) :
    (x : ℂ) ^ y = (-x : ℂ) ^ y * exp (π * I * y) := by
  rcases hx.eq_or_lt with (rfl | hlt)
  · rcases eq_or_ne y 0 with (rfl | hy) <;> simp [*]
  have hne : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hlt.ne
  rw [cpow_def_of_ne_zero hne, cpow_def_of_ne_zero (neg_ne_zero.2 hne), ← exp_add, ← add_mul, log,
    log, abs.map_neg, arg_ofReal_of_neg hlt, ← ofReal_neg,
    arg_ofReal_of_nonneg (neg_nonneg.2 hx), ofReal_zero, zero_mul, add_zero]
#align complex.of_real_cpow_of_nonpos Complex.ofReal_cpow_of_nonpos

lemma cpow_ofReal (x : ℂ) (y : ℝ) :
    x ^ (y : ℂ) = ↑(abs x ^ y) * (Real.cos (arg x * y) + Real.sin (arg x * y) * I) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [ofReal_cpow le_rfl]
  · rw [cpow_def_of_ne_zero hx, exp_eq_exp_re_mul_sin_add_cos, mul_comm (log x)]
    norm_cast
    rw [ofReal_mul_re, ofReal_mul_im, log_re, log_im, mul_comm y, mul_comm y, Real.exp_mul,
      Real.exp_log]
    rwa [abs.pos_iff]

lemma cpow_ofReal_re (x : ℂ) (y : ℝ) : (x ^ (y : ℂ)).re = (abs x) ^ y * Real.cos (arg x * y) := by
  rw [cpow_ofReal]; generalize arg x * y = z; simp [Real.cos]

lemma cpow_ofReal_im (x : ℂ) (y : ℝ) : (x ^ (y : ℂ)).im = (abs x) ^ y * Real.sin (arg x * y) := by
  rw [cpow_ofReal]; generalize arg x * y = z; simp [Real.sin]

theorem abs_cpow_of_ne_zero {z : ℂ} (hz : z ≠ 0) (w : ℂ) :
    abs (z ^ w) = abs z ^ w.re / Real.exp (arg z * im w) := by
  rw [cpow_def_of_ne_zero hz, abs_exp, mul_re, log_re, log_im, Real.exp_sub,
    Real.rpow_def_of_pos (abs.pos hz)]
#align complex.abs_cpow_of_ne_zero Complex.abs_cpow_of_ne_zero

theorem abs_cpow_of_imp {z w : ℂ} (h : z = 0 → w.re = 0 → w = 0) :
    abs (z ^ w) = abs z ^ w.re / Real.exp (arg z * im w) := by
  rcases ne_or_eq z 0 with (hz | rfl) <;> [exact abs_cpow_of_ne_zero hz w; rw [map_zero]]
  cases' eq_or_ne w.re 0 with hw hw
  · simp [hw, h rfl hw]
  · rw [Real.zero_rpow hw, zero_div, zero_cpow, map_zero]
    exact ne_of_apply_ne re hw
#align complex.abs_cpow_of_imp Complex.abs_cpow_of_imp

theorem abs_cpow_le (z w : ℂ) : abs (z ^ w) ≤ abs z ^ w.re / Real.exp (arg z * im w) := by
  by_cases h : z = 0 → w.re = 0 → w = 0
  · exact (abs_cpow_of_imp h).le
  · push_neg at h
    simp [h]
#align complex.abs_cpow_le Complex.abs_cpow_le

@[simp]
theorem abs_cpow_real (x : ℂ) (y : ℝ) : abs (x ^ (y : ℂ)) = Complex.abs x ^ y := by
  rw [abs_cpow_of_imp] <;> simp
#align complex.abs_cpow_real Complex.abs_cpow_real

@[simp]
theorem abs_cpow_inv_nat (x : ℂ) (n : ℕ) : abs (x ^ (n⁻¹ : ℂ)) = Complex.abs x ^ (n⁻¹ : ℝ) := by
  rw [← abs_cpow_real]; simp [-abs_cpow_real]
#align complex.abs_cpow_inv_nat Complex.abs_cpow_inv_nat

theorem abs_cpow_eq_rpow_re_of_pos {x : ℝ} (hx : 0 < x) (y : ℂ) : abs (x ^ y) = x ^ y.re := by
  rw [abs_cpow_of_ne_zero (ofReal_ne_zero.mpr hx.ne'), arg_ofReal_of_nonneg hx.le,
    zero_mul, Real.exp_zero, div_one, abs_of_nonneg hx.le]
#align complex.abs_cpow_eq_rpow_re_of_pos Complex.abs_cpow_eq_rpow_re_of_pos

theorem abs_cpow_eq_rpow_re_of_nonneg {x : ℝ} (hx : 0 ≤ x) {y : ℂ} (hy : re y ≠ 0) :
    abs (x ^ y) = x ^ re y := by
  rw [abs_cpow_of_imp] <;> simp [*, arg_ofReal_of_nonneg, _root_.abs_of_nonneg]
#align complex.abs_cpow_eq_rpow_re_of_nonneg Complex.abs_cpow_eq_rpow_re_of_nonneg

end Complex

/-!
## Further algebraic properties of `rpow`
-/


namespace Real

variable {x y z : ℝ}

theorem rpow_mul {x : ℝ} (hx : 0 ≤ x) (y z : ℝ) : x ^ (y * z) = (x ^ y) ^ z := by
  rw [← Complex.ofReal_inj, Complex.ofReal_cpow (rpow_nonneg_of_nonneg hx _),
      Complex.ofReal_cpow hx, Complex.ofReal_mul, Complex.cpow_mul, Complex.ofReal_cpow hx] <;>
    simp only [(Complex.ofReal_mul _ _).symm, (Complex.ofReal_log hx).symm, Complex.ofReal_im,
      neg_lt_zero, pi_pos, le_of_lt pi_pos]
#align real.rpow_mul Real.rpow_mul

theorem rpow_add_int {x : ℝ} (hx : x ≠ 0) (y : ℝ) (n : ℤ) : x ^ (y + n) = x ^ y * x ^ n :=
  by rw [rpow_def, rpow_def, Complex.ofReal_add,
    Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hx), Complex.ofReal_int_cast,
    Complex.cpow_int_cast, ← Complex.ofReal_zpow, mul_comm, Complex.ofReal_mul_re, mul_comm]
#align real.rpow_add_int Real.rpow_add_int

theorem rpow_add_nat {x : ℝ} (hx : x ≠ 0) (y : ℝ) (n : ℕ) : x ^ (y + n) = x ^ y * x ^ n :=
  by simpa using rpow_add_int hx y n
#align real.rpow_add_nat Real.rpow_add_nat

theorem rpow_sub_int {x : ℝ} (hx : x ≠ 0) (y : ℝ) (n : ℕ) : x ^ (y - n) = x ^ y / x ^ n :=
  by simpa using rpow_add_int hx y (-n)
#align real.rpow_sub_int Real.rpow_sub_int

theorem rpow_sub_nat {x : ℝ} (hx : x ≠ 0) (y : ℝ) (n : ℕ) : x ^ (y - n) = x ^ y / x ^ n :=
  by simpa using rpow_sub_int hx y n
#align real.rpow_sub_nat Real.rpow_sub_nat

theorem rpow_add_one {x : ℝ} (hx : x ≠ 0) (y : ℝ) : x ^ (y + 1) = x ^ y * x := by
  simpa using rpow_add_nat hx y 1
#align real.rpow_add_one Real.rpow_add_one

theorem rpow_sub_one {x : ℝ} (hx : x ≠ 0) (y : ℝ) : x ^ (y - 1) = x ^ y / x := by
  simpa using rpow_sub_nat hx y 1
#align real.rpow_sub_one Real.rpow_sub_one

@[simp, norm_cast]
theorem rpow_int_cast (x : ℝ) (n : ℤ) : x ^ (n : ℝ) = x ^ n := by
  simp only [rpow_def, ← Complex.ofReal_zpow, Complex.cpow_int_cast, Complex.ofReal_int_cast,
    Complex.ofReal_re]
#align real.rpow_int_cast Real.rpow_int_cast

@[simp, norm_cast]
theorem rpow_nat_cast (x : ℝ) (n : ℕ) : x ^ (n : ℝ) = x ^ n :=
  by simpa using rpow_int_cast x n
#align real.rpow_nat_cast Real.rpow_nat_cast

@[simp]
theorem rpow_two (x : ℝ) : x ^ (2 : ℝ) = x ^ 2 := by
  rw [← rpow_nat_cast]
  simp only [Nat.cast_ofNat]
#align real.rpow_two Real.rpow_two

theorem rpow_neg_one (x : ℝ) : x ^ (-1 : ℝ) = x⁻¹ := by
  suffices H : x ^ ((-1 : ℤ) : ℝ) = x⁻¹; · rwa [Int.cast_neg, Int.cast_one] at H
  simp only [rpow_int_cast, zpow_one, zpow_neg]
#align real.rpow_neg_one Real.rpow_neg_one

theorem mul_rpow {x y z : ℝ} (h : 0 ≤ x) (h₁ : 0 ≤ y) : (x * y) ^ z = x ^ z * y ^ z := by
  iterate 2 rw [Real.rpow_def_of_nonneg]; split_ifs with h_ifs <;> simp_all
  · exact h
  · rw [not_or] at h_ifs
    have hx : 0 < x := by
      cases' lt_or_eq_of_le h with h₂ h₂
      · exact h₂
      exfalso
      apply h_ifs.1
      exact Eq.symm h₂
    have hy : 0 < y := by
      cases' lt_or_eq_of_le h₁ with h₂ h₂
      · exact h₂
      exfalso
      apply h_ifs.2
      exact Eq.symm h₂
    rw [log_mul (ne_of_gt hx) (ne_of_gt hy), add_mul, exp_add, rpow_def_of_pos hx,
      rpow_def_of_pos hy]
  · exact mul_nonneg h h₁
#align real.mul_rpow Real.mul_rpow

theorem inv_rpow (hx : 0 ≤ x) (y : ℝ) : x⁻¹ ^ y = (x ^ y)⁻¹ := by
  simp only [← rpow_neg_one, ← rpow_mul hx, mul_comm]
#align real.inv_rpow Real.inv_rpow

theorem div_rpow (hx : 0 ≤ x) (hy : 0 ≤ y) (z : ℝ) : (x / y) ^ z = x ^ z / y ^ z := by
  simp only [div_eq_mul_inv, mul_rpow hx (inv_nonneg.2 hy), inv_rpow hy]
#align real.div_rpow Real.div_rpow

theorem log_rpow {x : ℝ} (hx : 0 < x) (y : ℝ) : log (x ^ y) = y * log x := by
  apply exp_injective
  rw [exp_log (rpow_pos_of_pos hx y), ← exp_log hx, mul_comm, rpow_def_of_pos (exp_pos (log x)) y]
#align real.log_rpow Real.log_rpow

theorem mul_log_eq_log_iff {x y z : ℝ} (hx : 0 < x) (hz : 0 < z) :
    y * log x = log z ↔ x ^ y = z :=
  ⟨fun h ↦ log_injOn_pos (rpow_pos_of_pos hx _) hz <| log_rpow hx _ |>.trans h,
  by rintro rfl; rw [log_rpow hx]⟩

/-! Note: lemmas about `(∏ i in s, f i ^ r)` such as `Real.finset_prod_rpow` are proved
in `Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean` instead. -/

/-!
## Order and monotonicity
-/


@[gcongr]
theorem rpow_lt_rpow (hx : 0 ≤ x) (hxy : x < y) (hz : 0 < z) : x ^ z < y ^ z := by
  rw [le_iff_eq_or_lt] at hx; cases' hx with hx hx
  · rw [← hx, zero_rpow (ne_of_gt hz)]
    exact rpow_pos_of_pos (by rwa [← hx] at hxy) _
  · rw [rpow_def_of_pos hx, rpow_def_of_pos (lt_trans hx hxy), exp_lt_exp]
    exact mul_lt_mul_of_pos_right (log_lt_log hx hxy) hz
#align real.rpow_lt_rpow Real.rpow_lt_rpow

theorem strictMonoOn_rpow_Ici_of_exponent_pos {r : ℝ} (hr : 0 < r) :
    StrictMonoOn (fun (x : ℝ) => x ^ r) (Set.Ici 0) :=
  fun _ ha _ _ hab => rpow_lt_rpow ha hab hr

@[gcongr]
theorem rpow_le_rpow {x y z : ℝ} (h : 0 ≤ x) (h₁ : x ≤ y) (h₂ : 0 ≤ z) : x ^ z ≤ y ^ z := by
  rcases eq_or_lt_of_le h₁ with (rfl | h₁'); · rfl
  rcases eq_or_lt_of_le h₂ with (rfl | h₂'); · simp
  exact le_of_lt (rpow_lt_rpow h h₁' h₂')
#align real.rpow_le_rpow Real.rpow_le_rpow

theorem monotoneOn_rpow_Ici_of_exponent_nonneg {r : ℝ} (hr : 0 ≤ r) :
    MonotoneOn (fun (x : ℝ) => x ^ r) (Set.Ici 0) :=
  fun _ ha _ _ hab => rpow_le_rpow ha hab hr

theorem rpow_lt_rpow_iff (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 < z) : x ^ z < y ^ z ↔ x < y :=
  ⟨lt_imp_lt_of_le_imp_le fun h => rpow_le_rpow hy h (le_of_lt hz), fun h => rpow_lt_rpow hx h hz⟩
#align real.rpow_lt_rpow_iff Real.rpow_lt_rpow_iff

theorem rpow_le_rpow_iff (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 < z) : x ^ z ≤ y ^ z ↔ x ≤ y :=
  le_iff_le_iff_lt_iff_lt.2 <| rpow_lt_rpow_iff hy hx hz
#align real.rpow_le_rpow_iff Real.rpow_le_rpow_iff

theorem le_rpow_inv_iff_of_neg (hx : 0 < x) (hy : 0 < y) (hz : z < 0) :
    x ≤ y ^ z⁻¹ ↔ y ≤ x ^ z := by
  have hz' : 0 < -z := by rwa [lt_neg, neg_zero]
  have hxz : 0 < x ^ (-z) := Real.rpow_pos_of_pos hx _
  have hyz : 0 < y ^ z⁻¹ := Real.rpow_pos_of_pos hy _
  rw [← Real.rpow_le_rpow_iff hx.le hyz.le hz', ← Real.rpow_mul hy.le]
  simp only [ne_of_lt hz, Real.rpow_neg_one, mul_neg, inv_mul_cancel, Ne.def, not_false_iff]
  rw [le_inv hxz hy, ← Real.rpow_neg_one, ← Real.rpow_mul hx.le]
  simp
#align real.le_rpow_inv_iff_of_neg Real.le_rpow_inv_iff_of_neg

theorem lt_rpow_inv_iff_of_neg (hx : 0 < x) (hy : 0 < y) (hz : z < 0) :
    x < y ^ z⁻¹ ↔ y < x ^ z := by
  have hz' : 0 < -z := by rwa [lt_neg, neg_zero]
  have hxz : 0 < x ^ (-z) := Real.rpow_pos_of_pos hx _
  have hyz : 0 < y ^ z⁻¹ := Real.rpow_pos_of_pos hy _
  rw [← Real.rpow_lt_rpow_iff hx.le hyz.le hz', ← Real.rpow_mul hy.le]
  simp only [ne_of_lt hz, Real.rpow_neg_one, mul_neg, inv_mul_cancel, Ne.def, not_false_iff]
  rw [lt_inv hxz hy, ← Real.rpow_neg_one, ← Real.rpow_mul hx.le]
  simp
#align real.lt_rpow_inv_iff_of_neg Real.lt_rpow_inv_iff_of_neg

theorem rpow_inv_lt_iff_of_neg (hx : 0 < x) (hy : 0 < y) (hz : z < 0) :
    x ^ z⁻¹ < y ↔ y ^ z < x := by
    convert lt_rpow_inv_iff_of_neg (Real.rpow_pos_of_pos hx z⁻¹) (Real.rpow_pos_of_pos hy z) hz <;>
    simp [← Real.rpow_mul hx.le, ← Real.rpow_mul hy.le, ne_of_lt hz]
#align real.rpow_inv_lt_iff_of_neg Real.rpow_inv_lt_iff_of_neg

theorem rpow_inv_le_iff_of_neg (hx : 0 < x) (hy : 0 < y) (hz : z < 0) :
    x ^ z⁻¹ ≤ y ↔ y ^ z ≤ x := by
  convert le_rpow_inv_iff_of_neg (Real.rpow_pos_of_pos hx z⁻¹) (Real.rpow_pos_of_pos hy z) hz <;>
  simp [← Real.rpow_mul hx.le, ← Real.rpow_mul hy.le, ne_of_lt hz]
#align real.rpow_inv_le_iff_of_neg Real.rpow_inv_le_iff_of_neg

theorem rpow_lt_rpow_of_exponent_lt (hx : 1 < x) (hyz : y < z) : x ^ y < x ^ z := by
  repeat' rw [rpow_def_of_pos (lt_trans zero_lt_one hx)]
  rw [exp_lt_exp]; exact mul_lt_mul_of_pos_left hyz (log_pos hx)
#align real.rpow_lt_rpow_of_exponent_lt Real.rpow_lt_rpow_of_exponent_lt

@[gcongr]
theorem rpow_le_rpow_of_exponent_le (hx : 1 ≤ x) (hyz : y ≤ z) : x ^ y ≤ x ^ z := by
  repeat' rw [rpow_def_of_pos (lt_of_lt_of_le zero_lt_one hx)]
  rw [exp_le_exp]; exact mul_le_mul_of_nonneg_left hyz (log_nonneg hx)
#align real.rpow_le_rpow_of_exponent_le Real.rpow_le_rpow_of_exponent_le

theorem rpow_lt_rpow_of_exponent_neg {x y z : ℝ} (hy : 0 < y) (hxy : y < x) (hz : z < 0) :
    x ^ z < y ^ z := by
  have hx : 0 < x := hy.trans hxy
  rw [←neg_neg z, Real.rpow_neg (le_of_lt hx) (-z), Real.rpow_neg (le_of_lt hy) (-z),
      inv_lt_inv (rpow_pos_of_pos hx _) (rpow_pos_of_pos hy _)]
  exact Real.rpow_lt_rpow (by positivity) hxy <| neg_pos_of_neg hz

theorem strictAntiOn_rpow_Ioi_of_exponent_neg {r : ℝ} (hr : r < 0) :
    StrictAntiOn (fun (x:ℝ) => x ^ r) (Set.Ioi 0) :=
  fun _ ha _ _ hab => rpow_lt_rpow_of_exponent_neg ha hab hr

theorem rpow_le_rpow_of_exponent_nonpos {x y : ℝ} (hy : 0 < y) (hxy : y ≤ x) (hz : z ≤ 0) :
    x ^ z ≤ y ^ z := by
  rcases ne_or_eq z 0 with hz_zero | rfl
  case inl =>
    rcases ne_or_eq x y with hxy' | rfl
    case inl =>
      exact le_of_lt <| rpow_lt_rpow_of_exponent_neg hy (Ne.lt_of_le (id (Ne.symm hxy')) hxy)
        (Ne.lt_of_le hz_zero hz)
    case inr => simp
  case inr => simp

theorem antitoneOn_rpow_Ioi_of_exponent_nonpos {r : ℝ} (hr : r ≤ 0) :
    AntitoneOn (fun (x:ℝ) => x ^ r) (Set.Ioi 0) :=
  fun _ ha _ _ hab => rpow_le_rpow_of_exponent_nonpos ha hab hr

@[simp]
theorem rpow_le_rpow_left_iff (hx : 1 < x) : x ^ y ≤ x ^ z ↔ y ≤ z := by
  have x_pos : 0 < x := lt_trans zero_lt_one hx
  rw [← log_le_log (rpow_pos_of_pos x_pos y) (rpow_pos_of_pos x_pos z), log_rpow x_pos,
    log_rpow x_pos, mul_le_mul_right (log_pos hx)]
#align real.rpow_le_rpow_left_iff Real.rpow_le_rpow_left_iff

@[simp]
theorem rpow_lt_rpow_left_iff (hx : 1 < x) : x ^ y < x ^ z ↔ y < z := by
  rw [lt_iff_not_le, rpow_le_rpow_left_iff hx, lt_iff_not_le]
#align real.rpow_lt_rpow_left_iff Real.rpow_lt_rpow_left_iff

theorem rpow_lt_rpow_of_exponent_gt (hx0 : 0 < x) (hx1 : x < 1) (hyz : z < y) : x ^ y < x ^ z := by
  repeat' rw [rpow_def_of_pos hx0]
  rw [exp_lt_exp]; exact mul_lt_mul_of_neg_left hyz (log_neg hx0 hx1)
#align real.rpow_lt_rpow_of_exponent_gt Real.rpow_lt_rpow_of_exponent_gt

theorem rpow_le_rpow_of_exponent_ge (hx0 : 0 < x) (hx1 : x ≤ 1) (hyz : z ≤ y) : x ^ y ≤ x ^ z := by
  repeat' rw [rpow_def_of_pos hx0]
  rw [exp_le_exp]; exact mul_le_mul_of_nonpos_left hyz (log_nonpos (le_of_lt hx0) hx1)
#align real.rpow_le_rpow_of_exponent_ge Real.rpow_le_rpow_of_exponent_ge

@[simp]
theorem rpow_le_rpow_left_iff_of_base_lt_one (hx0 : 0 < x) (hx1 : x < 1) :
    x ^ y ≤ x ^ z ↔ z ≤ y := by
  rw [← log_le_log (rpow_pos_of_pos hx0 y) (rpow_pos_of_pos hx0 z), log_rpow hx0, log_rpow hx0,
    mul_le_mul_right_of_neg (log_neg hx0 hx1)]
#align real.rpow_le_rpow_left_iff_of_base_lt_one Real.rpow_le_rpow_left_iff_of_base_lt_one

@[simp]
theorem rpow_lt_rpow_left_iff_of_base_lt_one (hx0 : 0 < x) (hx1 : x < 1) : x ^ y < x ^ z ↔ z < y :=
  by rw [lt_iff_not_le, rpow_le_rpow_left_iff_of_base_lt_one hx0 hx1, lt_iff_not_le]
#align real.rpow_lt_rpow_left_iff_of_base_lt_one Real.rpow_lt_rpow_left_iff_of_base_lt_one

theorem rpow_lt_one {x z : ℝ} (hx1 : 0 ≤ x) (hx2 : x < 1) (hz : 0 < z) : x ^ z < 1 := by
  rw [← one_rpow z]
  exact rpow_lt_rpow hx1 hx2 hz
#align real.rpow_lt_one Real.rpow_lt_one

theorem rpow_le_one {x z : ℝ} (hx1 : 0 ≤ x) (hx2 : x ≤ 1) (hz : 0 ≤ z) : x ^ z ≤ 1 := by
  rw [← one_rpow z]
  exact rpow_le_rpow hx1 hx2 hz
#align real.rpow_le_one Real.rpow_le_one

theorem rpow_lt_one_of_one_lt_of_neg {x z : ℝ} (hx : 1 < x) (hz : z < 0) : x ^ z < 1 := by
  convert rpow_lt_rpow_of_exponent_lt hx hz
  exact (rpow_zero x).symm
#align real.rpow_lt_one_of_one_lt_of_neg Real.rpow_lt_one_of_one_lt_of_neg

theorem rpow_le_one_of_one_le_of_nonpos {x z : ℝ} (hx : 1 ≤ x) (hz : z ≤ 0) : x ^ z ≤ 1 := by
  convert rpow_le_rpow_of_exponent_le hx hz
  exact (rpow_zero x).symm
#align real.rpow_le_one_of_one_le_of_nonpos Real.rpow_le_one_of_one_le_of_nonpos

theorem one_lt_rpow {x z : ℝ} (hx : 1 < x) (hz : 0 < z) : 1 < x ^ z := by
  rw [← one_rpow z]
  exact rpow_lt_rpow zero_le_one hx hz
#align real.one_lt_rpow Real.one_lt_rpow

theorem one_le_rpow {x z : ℝ} (hx : 1 ≤ x) (hz : 0 ≤ z) : 1 ≤ x ^ z := by
  rw [← one_rpow z]
  exact rpow_le_rpow zero_le_one hx hz
#align real.one_le_rpow Real.one_le_rpow

theorem one_lt_rpow_of_pos_of_lt_one_of_neg (hx1 : 0 < x) (hx2 : x < 1) (hz : z < 0) :
    1 < x ^ z := by
  convert rpow_lt_rpow_of_exponent_gt hx1 hx2 hz
  exact (rpow_zero x).symm
#align real.one_lt_rpow_of_pos_of_lt_one_of_neg Real.one_lt_rpow_of_pos_of_lt_one_of_neg

theorem one_le_rpow_of_pos_of_le_one_of_nonpos (hx1 : 0 < x) (hx2 : x ≤ 1) (hz : z ≤ 0) :
    1 ≤ x ^ z := by
  convert rpow_le_rpow_of_exponent_ge hx1 hx2 hz
  exact (rpow_zero x).symm
#align real.one_le_rpow_of_pos_of_le_one_of_nonpos Real.one_le_rpow_of_pos_of_le_one_of_nonpos

theorem rpow_lt_one_iff_of_pos (hx : 0 < x) : x ^ y < 1 ↔ 1 < x ∧ y < 0 ∨ x < 1 ∧ 0 < y := by
  rw [rpow_def_of_pos hx, exp_lt_one_iff, mul_neg_iff, log_pos_iff hx, log_neg_iff hx]
#align real.rpow_lt_one_iff_of_pos Real.rpow_lt_one_iff_of_pos

theorem rpow_lt_one_iff (hx : 0 ≤ x) :
    x ^ y < 1 ↔ x = 0 ∧ y ≠ 0 ∨ 1 < x ∧ y < 0 ∨ x < 1 ∧ 0 < y := by
  rcases hx.eq_or_lt with (rfl | hx)
  · rcases _root_.em (y = 0) with (rfl | hy) <;> simp [*, lt_irrefl, zero_lt_one]
  · simp [rpow_lt_one_iff_of_pos hx, hx.ne.symm]
#align real.rpow_lt_one_iff Real.rpow_lt_one_iff

theorem one_lt_rpow_iff_of_pos (hx : 0 < x) : 1 < x ^ y ↔ 1 < x ∧ 0 < y ∨ x < 1 ∧ y < 0 := by
  rw [rpow_def_of_pos hx, one_lt_exp_iff, mul_pos_iff, log_pos_iff hx, log_neg_iff hx]
#align real.one_lt_rpow_iff_of_pos Real.one_lt_rpow_iff_of_pos

theorem one_lt_rpow_iff (hx : 0 ≤ x) : 1 < x ^ y ↔ 1 < x ∧ 0 < y ∨ 0 < x ∧ x < 1 ∧ y < 0 := by
  rcases hx.eq_or_lt with (rfl | hx)
  · rcases _root_.em (y = 0) with (rfl | hy) <;> simp [*, lt_irrefl, (zero_lt_one' ℝ).not_lt]
  · simp [one_lt_rpow_iff_of_pos hx, hx]
#align real.one_lt_rpow_iff Real.one_lt_rpow_iff

theorem rpow_le_rpow_of_exponent_ge' (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hz : 0 ≤ z) (hyz : z ≤ y) :
    x ^ y ≤ x ^ z := by
  rcases eq_or_lt_of_le hx0 with (rfl | hx0')
  · rcases eq_or_lt_of_le hz with (rfl | hz')
    · exact (rpow_zero 0).symm ▸ rpow_le_one hx0 hx1 hyz
    rw [zero_rpow, zero_rpow] <;> linarith
  · exact rpow_le_rpow_of_exponent_ge hx0' hx1 hyz
#align real.rpow_le_rpow_of_exponent_ge' Real.rpow_le_rpow_of_exponent_ge'

theorem rpow_left_injOn {x : ℝ} (hx : x ≠ 0) : InjOn (fun y : ℝ => y ^ x) { y : ℝ | 0 ≤ y } := by
  rintro y hy z hz (hyz : y ^ x = z ^ x)
  rw [← rpow_one y, ← rpow_one z, ← _root_.mul_inv_cancel hx, rpow_mul hy, rpow_mul hz, hyz]
#align real.rpow_left_inj_on Real.rpow_left_injOn

theorem le_rpow_iff_log_le (hx : 0 < x) (hy : 0 < y) : x ≤ y ^ z ↔ Real.log x ≤ z * Real.log y := by
  rw [← Real.log_le_log hx (Real.rpow_pos_of_pos hy z), Real.log_rpow hy]
#align real.le_rpow_iff_log_le Real.le_rpow_iff_log_le

theorem le_rpow_of_log_le (hx : 0 ≤ x) (hy : 0 < y) (h : Real.log x ≤ z * Real.log y) :
    x ≤ y ^ z := by
  obtain hx | rfl := hx.lt_or_eq
  · exact (le_rpow_iff_log_le hx hy).2 h
  exact (Real.rpow_pos_of_pos hy z).le
#align real.le_rpow_of_log_le Real.le_rpow_of_log_le

theorem lt_rpow_iff_log_lt (hx : 0 < x) (hy : 0 < y) : x < y ^ z ↔ Real.log x < z * Real.log y := by
  rw [← Real.log_lt_log_iff hx (Real.rpow_pos_of_pos hy z), Real.log_rpow hy]
#align real.lt_rpow_iff_log_lt Real.lt_rpow_iff_log_lt

theorem lt_rpow_of_log_lt (hx : 0 ≤ x) (hy : 0 < y) (h : Real.log x < z * Real.log y) :
    x < y ^ z := by
  obtain hx | rfl := hx.lt_or_eq
  · exact (lt_rpow_iff_log_lt hx hy).2 h
  exact Real.rpow_pos_of_pos hy z
#align real.lt_rpow_of_log_lt Real.lt_rpow_of_log_lt

theorem rpow_le_one_iff_of_pos (hx : 0 < x) : x ^ y ≤ 1 ↔ 1 ≤ x ∧ y ≤ 0 ∨ x ≤ 1 ∧ 0 ≤ y := by
  rw [rpow_def_of_pos hx, exp_le_one_iff, mul_nonpos_iff, log_nonneg_iff hx, log_nonpos_iff hx]
#align real.rpow_le_one_iff_of_pos Real.rpow_le_one_iff_of_pos

/-- Bound for `|log x * x ^ t|` in the interval `(0, 1]`, for positive real `t`. -/
theorem abs_log_mul_self_rpow_lt (x t : ℝ) (h1 : 0 < x) (h2 : x ≤ 1) (ht : 0 < t) :
    |log x * x ^ t| < 1 / t := by
  rw [lt_div_iff ht]
  have := abs_log_mul_self_lt (x ^ t) (rpow_pos_of_pos h1 t) (rpow_le_one h1.le h2 ht.le)
  rwa [log_rpow h1, mul_assoc, abs_mul, abs_of_pos ht, mul_comm] at this
#align real.abs_log_mul_self_rpow_lt Real.abs_log_mul_self_rpow_lt

theorem pow_nat_rpow_nat_inv {x : ℝ} (hx : 0 ≤ x) {n : ℕ} (hn : n ≠ 0) :
    (x ^ n) ^ (n⁻¹ : ℝ) = x := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  rw [← rpow_nat_cast, ← rpow_mul hx, mul_inv_cancel hn0, rpow_one]
#align real.pow_nat_rpow_nat_inv Real.pow_nat_rpow_nat_inv

theorem rpow_nat_inv_pow_nat {x : ℝ} (hx : 0 ≤ x) {n : ℕ} (hn : n ≠ 0) :
    (x ^ (n⁻¹ : ℝ)) ^ n = x := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  rw [← rpow_nat_cast, ← rpow_mul hx, inv_mul_cancel hn0, rpow_one]
#align real.rpow_nat_inv_pow_nat Real.rpow_nat_inv_pow_nat

lemma strictMono_rpow_of_base_gt_one {b : ℝ} (hb : 1 < b) :
    StrictMono (rpow b) := by
  show StrictMono (fun (x:ℝ) => b ^ x)
  simp_rw [Real.rpow_def_of_pos (zero_lt_one.trans hb)]
  exact exp_strictMono.comp <| StrictMono.const_mul strictMono_id <| Real.log_pos hb

lemma monotone_rpow_of_base_ge_one {b : ℝ} (hb : 1 ≤ b) :
    Monotone (rpow b) := by
  rcases lt_or_eq_of_le hb with hb | rfl
  case inl => exact (strictMono_rpow_of_base_gt_one hb).monotone
  case inr => intro _ _ _; simp

lemma strictAnti_rpow_of_base_lt_one {b : ℝ} (hb₀ : 0 < b) (hb₁ : b < 1) :
    StrictAnti (rpow b) := by
  show StrictAnti (fun (x:ℝ) => b ^ x)
  simp_rw [Real.rpow_def_of_pos hb₀]
  exact exp_strictMono.comp_strictAnti <| StrictMono.const_mul_of_neg strictMono_id
      <| Real.log_neg hb₀ hb₁

lemma antitone_rpow_of_base_le_one {b : ℝ} (hb₀ : 0 < b) (hb₁ : b ≤ 1) :
    Antitone (rpow b) := by
  rcases lt_or_eq_of_le hb₁ with hb₁ | rfl
  case inl => exact (strictAnti_rpow_of_base_lt_one hb₀ hb₁).antitone
  case inr => intro _ _ _; simp

end Real

/-!
## Square roots of reals
-/


namespace Real

variable {z x y : ℝ}

section Sqrt

theorem sqrt_eq_rpow (x : ℝ) : sqrt x = x ^ (1 / (2 : ℝ)) := by
  obtain h | h := le_or_lt 0 x
  · rw [← mul_self_inj_of_nonneg (sqrt_nonneg _) (rpow_nonneg_of_nonneg h _), mul_self_sqrt h, ← sq,
      ← rpow_nat_cast, ← rpow_mul h]
    norm_num
  · have : 1 / (2 : ℝ) * π = π / (2 : ℝ) := by ring
    rw [sqrt_eq_zero_of_nonpos h.le, rpow_def_of_neg h, this, cos_pi_div_two, mul_zero]
#align real.sqrt_eq_rpow Real.sqrt_eq_rpow

theorem rpow_div_two_eq_sqrt {x : ℝ} (r : ℝ) (hx : 0 ≤ x) : x ^ (r / 2) = sqrt x ^ r := by
  rw [sqrt_eq_rpow, ← rpow_mul hx]
  congr
  ring
#align real.rpow_div_two_eq_sqrt Real.rpow_div_two_eq_sqrt

end Sqrt

variable {n : ℕ}

theorem exists_rat_pow_btwn_rat_aux (hn : n ≠ 0) (x y : ℝ) (h : x < y) (hy : 0 < y) :
    ∃ q : ℚ, 0 < q ∧ x < (q : ℝ) ^ n ∧ (q : ℝ) ^ n < y := by
  have hn' : 0 < (n : ℝ) := mod_cast hn.bot_lt
  obtain ⟨q, hxq, hqy⟩ :=
    exists_rat_btwn (rpow_lt_rpow (le_max_left 0 x) (max_lt hy h) <| inv_pos.mpr hn')
  have := rpow_nonneg_of_nonneg (le_max_left 0 x) n⁻¹
  have hq := this.trans_lt hxq
  replace hxq := rpow_lt_rpow this hxq hn'
  replace hqy := rpow_lt_rpow hq.le hqy hn'
  rw [rpow_nat_cast, rpow_nat_cast, rpow_nat_inv_pow_nat _ hn] at hxq hqy
  · exact ⟨q, mod_cast hq, (le_max_right _ _).trans_lt hxq, hqy⟩
  · exact hy.le
  · exact le_max_left _ _
#align real.exists_rat_pow_btwn_rat_aux Real.exists_rat_pow_btwn_rat_aux

theorem exists_rat_pow_btwn_rat (hn : n ≠ 0) {x y : ℚ} (h : x < y) (hy : 0 < y) :
    ∃ q : ℚ, 0 < q ∧ x < q ^ n ∧ q ^ n < y := by
  apply_mod_cast exists_rat_pow_btwn_rat_aux hn x y <;> assumption
#align real.exists_rat_pow_btwn_rat Real.exists_rat_pow_btwn_rat

/-- There is a rational power between any two positive elements of an archimedean ordered field. -/
theorem exists_rat_pow_btwn {α : Type*} [LinearOrderedField α] [Archimedean α] (hn : n ≠ 0)
    {x y : α} (h : x < y) (hy : 0 < y) : ∃ q : ℚ, 0 < q ∧ x < (q : α) ^ n ∧ (q : α) ^ n < y := by
  obtain ⟨q₂, hx₂, hy₂⟩ := exists_rat_btwn (max_lt h hy)
  obtain ⟨q₁, hx₁, hq₁₂⟩ := exists_rat_btwn hx₂
  have : (0 : α) < q₂ := (le_max_right _ _).trans_lt hx₂
  norm_cast at hq₁₂ this
  obtain ⟨q, hq, hq₁, hq₂⟩ := exists_rat_pow_btwn_rat hn hq₁₂ this
  refine' ⟨q, hq, (le_max_left _ _).trans_lt <| hx₁.trans _, hy₂.trans' _⟩ <;> assumption_mod_cast
#align real.exists_rat_pow_btwn Real.exists_rat_pow_btwn

end Real

namespace Complex

lemma cpow_inv_two_re (x : ℂ) : (x ^ (2⁻¹ : ℂ)).re = sqrt ((abs x + x.re) / 2) := by
  rw [← ofReal_ofNat, ← ofReal_inv, cpow_ofReal_re, ← div_eq_mul_inv, ← one_div,
    ← Real.sqrt_eq_rpow, cos_half, ← sqrt_mul, ← mul_div_assoc, mul_add, mul_one, abs_mul_cos_arg]
  exacts [abs.nonneg _, (neg_pi_lt_arg _).le, arg_le_pi _]

lemma cpow_inv_two_im_eq_sqrt {x : ℂ} (hx : 0 ≤ x.im) :
    (x ^ (2⁻¹ : ℂ)).im = sqrt ((abs x - x.re) / 2) := by
  rw [← ofReal_ofNat, ← ofReal_inv, cpow_ofReal_im, ← div_eq_mul_inv, ← one_div,
    ← Real.sqrt_eq_rpow, sin_half_eq_sqrt, ← sqrt_mul (abs.nonneg _), ← mul_div_assoc, mul_sub,
    mul_one, abs_mul_cos_arg]
  · rwa [arg_nonneg_iff]
  · linarith [pi_pos, arg_le_pi x]

lemma cpow_inv_two_im_eq_neg_sqrt {x : ℂ} (hx : x.im < 0) :
    (x ^ (2⁻¹ : ℂ)).im = -sqrt ((abs x - x.re) / 2) := by
  rw [← ofReal_ofNat, ← ofReal_inv, cpow_ofReal_im, ← div_eq_mul_inv, ← one_div,
    ← Real.sqrt_eq_rpow, sin_half_eq_neg_sqrt, mul_neg, ← sqrt_mul (abs.nonneg _),
    ← mul_div_assoc, mul_sub, mul_one, abs_mul_cos_arg]
  · linarith [pi_pos, neg_pi_lt_arg x]
  · exact (arg_neg_iff.2 hx).le

lemma abs_cpow_inv_two_im (x : ℂ) : |(x ^ (2⁻¹ : ℂ)).im| = sqrt ((abs x - x.re) / 2) := by
  rw [← ofReal_ofNat, ← ofReal_inv, cpow_ofReal_im, ← div_eq_mul_inv, ← one_div,
    ← Real.sqrt_eq_rpow, _root_.abs_mul, _root_.abs_of_nonneg (sqrt_nonneg _), abs_sin_half,
    ← sqrt_mul (abs.nonneg _), ← mul_div_assoc, mul_sub, mul_one, abs_mul_cos_arg]

end Complex

section Tactics

/-!
## Tactic extensions for real powers
-/


-- namespace NormNum

-- open Tactic

-- theorem rpow_pos (a b : ℝ) (b' : ℕ) (c : ℝ) (hb : (b' : ℝ) = b) (h : a ^ b' = c) :
-- a ^ b = c := by
--   rw [← h, ← hb, Real.rpow_nat_cast]
-- #align norm_num.rpow_pos NormNum.rpow_pos

-- theorem rpow_neg (a b : ℝ) (b' : ℕ) (c c' : ℝ) (a0 : 0 ≤ a) (hb : (b' : ℝ) = b) (h : a ^ b' = c)
--     (hc : c⁻¹ = c') : a ^ (-b) = c' := by
--   rw [← hc, ← h, ← hb, Real.rpow_neg a0, Real.rpow_nat_cast]
-- #align norm_num.rpow_neg NormNum.rpow_neg

-- /-- Evaluate `Real.rpow a b` where `a` is a rational numeral and `b` is an integer.
-- (This cannot go via the generalized version `prove_rpow'` because `rpow_pos` has a
-- side condition; we do not attempt to evaluate `a ^ b` where `a` and `b` are both negative because
-- it comes out to some garbage.) -/
-- unsafe def prove_rpow (a b : expr) : tactic (expr × expr) := do
--   let na ← a.to_rat
--   let ic ← mk_instance_cache q(ℝ)
--   match match_sign b with
--     | Sum.inl b => do
--       let (ic, a0) ← guard (na ≥ 0) >> prove_nonneg ic a
--       let nc ← mk_instance_cache q(ℕ)
--       let (ic, nc, b', hb) ← prove_nat_uncast ic nc b
--       let (ic, c, h) ← prove_pow a na ic b'
--       let cr ← c
--       let (ic, c', hc) ← prove_inv ic c cr
--       pure (c', (expr.const `` rpow_neg []).mk_app [a, b, b', c, c', a0, hb, h, hc])
--     | Sum.inr ff => pure (q((1 : ℝ)), expr.const `` Real.rpow_zero [] a)
--     | Sum.inr tt => do
--       let nc ← mk_instance_cache q(ℕ)
--       let (ic, nc, b', hb) ← prove_nat_uncast ic nc b
--       let (ic, c, h) ← prove_pow a na ic b'
--       pure (c, (expr.const `` rpow_pos []).mk_app [a, b, b', c, hb, h])
-- #align norm_num.prove_rpow norm_num.prove_rpow

-- /-- Evaluates expressions of the form `rpow a b` and `a ^ b` in the special case where
-- `b` is an integer and `a` is a positive rational (so it's really just a rational power). -/
-- @[norm_num]
-- unsafe def eval_rpow : expr → tactic (expr × expr)
--   | q(@Pow.pow _ _ Real.hasPow $(a) $(b)) => b.to_int >> prove_rpow a b
--   | q(Real.rpow $(a) $(b)) => b.to_int >> prove_rpow a b
--   | _ => tactic.failed
-- #align norm_num.eval_rpow norm_num.eval_rpow

-- end NormNum

namespace Mathlib.Meta.Positivity

open Lean Meta Qq

/-- Extension for the `positivity` tactic: exponentiation by a real number is positive (namely 1)
when the exponent is zero. The other cases are done in `evalRpow`. -/
@[positivity (_ : ℝ) ^ (0 : ℝ), Pow.pow (_ : ℝ) (0 : ℝ), Real.rpow (_ : ℝ) (0 : ℝ)]
def evalRpowZero : Mathlib.Meta.Positivity.PositivityExt where eval {_ _} _ _ e := do
  let .app (.app (f : Q(ℝ → ℝ → ℝ)) (a : Q(ℝ))) (_ : Q(ℝ)) ← withReducible (whnf e)
    | throwError "not Real.rpow"
  guard <|← withDefault <| withNewMCtxDepth <| isDefEq f q(Real.rpow)
  pure (.positive (q(Real.rpow_zero_pos $a) : Expr))

/-- Extension for the `positivity` tactic: exponentiation by a real number is nonnegative when
the base is nonnegative and positive when the base is positive. -/
@[positivity (_ : ℝ) ^ (_ : ℝ), Pow.pow (_ : ℝ) (_ : ℝ), Real.rpow (_ : ℝ) (_ : ℝ)]
def evalRpow : Mathlib.Meta.Positivity.PositivityExt where eval {_ _} zα pα e := do
  let .app (.app (f : Q(ℝ → ℝ → ℝ)) (a : Q(ℝ))) (b : Q(ℝ)) ← withReducible (whnf e)
    | throwError "not Real.rpow"
  guard <|← withDefault <| withNewMCtxDepth <| isDefEq f q(Real.rpow)
  let ra ← core zα pα a
  match ra with
  | .positive pa =>
      have pa' : Q(0 < $a) := pa
      pure (.positive (q(Real.rpow_pos_of_pos $pa' $b) : Expr))
  | .nonnegative pa =>
      have pa' : Q(0 ≤ $a) := pa
      pure (.nonnegative (q(Real.rpow_nonneg_of_nonneg $pa' $b) : Expr))
  | _ => pure .none

end Mathlib.Meta.Positivity

end Tactics
