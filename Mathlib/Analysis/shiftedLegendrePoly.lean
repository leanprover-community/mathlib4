/-
Copyright (c) 2024 Junqi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junqi Liu
-/
import Mathlib

/-!
# shifted Legendre Polynomials

In this file, we define the shifted Legendre polynomials `shiftedLegendre n` for `n : ℕ` as a
polynomial in `ℝ[X]`. We prove some basic properties of the Legendre polynomials.

-/

open scoped Nat
open BigOperators Finset

variable {R : Type*}

namespace Polynomial

/--  `shiftedLegendre n` is the polynomial defined in terms of derivatives of order n.  -/
noncomputable def shiftedLegendre (n : ℕ) : ℝ[X] :=
  C (n ! : ℝ)⁻¹ * derivative^[n] (X ^ n * (1 - X) ^ n)

/-- The expand of `shiftedLegendre n`. -/
theorem shiftedLegendre_eq_sum (n : ℕ) : shiftedLegendre n = ∑ k ∈ Finset.range (n + 1),
    C ((-1) ^ k : ℝ) • (Nat.choose n k) * (Nat.choose (n + k) n) * X ^ k := by
  have h : ((X : ℝ[X]) - X ^ 2) ^ n =
    ∑ m ∈ range (n + 1), n.choose m • (- 1) ^ m * X ^ (n + m) := by
    rw[sub_eq_add_neg, add_comm, add_pow]
    congr! 1 with m hm
    rw[neg_pow, pow_two, mul_pow,← mul_assoc, mul_comm, mul_assoc, pow_mul_pow_sub, mul_assoc,
      ← pow_add, ← mul_assoc, nsmul_eq_mul, add_comm]
    rw[Finset.mem_range] at hm
    linarith
  rw [shiftedLegendre, ← mul_pow, mul_one_sub, ← pow_two, h, iterate_derivative_sum,
    Finset.mul_sum]
  congr! 1 with x _
  rw [show (n.choose x • (-1) ^ x : ℝ[X]) = C (n.choose x • (-1) ^ x) by simp,
    Polynomial.iterate_derivative_C_mul, Polynomial.iterate_derivative_X_pow_eq_smul,
    Nat.descFactorial_eq_div (by omega), show n + x - n = x by omega, smul_eq_mul, nsmul_eq_mul,
    ← mul_assoc, mul_assoc, mul_comm]
  simp only [map_mul, map_natCast, map_pow, map_neg, map_one, Algebra.mul_smul_comm,
    Algebra.smul_mul_assoc, X_pow_mul_assoc_C]
  rw [Algebra.smul_def, algebraMap_eq, map_natCast, add_comm, Nat.add_choose, ← mul_assoc,
    ← mul_assoc]
  congr 1
  rw [mul_rotate, mul_assoc]
  nth_rewrite 2 [mul_comm]
  congr
  apply Polynomial.ext
  intro m
  simp only [one_div, coeff_mul_C, coeff_natCast_ite, Nat.cast_ite, CharP.cast_eq_zero, ite_mul,
    zero_mul]
  by_cases h : m = 0
  · simp [h]
    rw [Nat.cast_div]
    · rw [← one_div, Nat.cast_div, Nat.cast_mul, div_mul_eq_div_mul_one_div]
      · field_simp
        left
        rw [mul_comm]
      · exact Nat.factorial_mul_factorial_dvd_factorial_add x n
      · norm_cast
        apply mul_ne_zero (Nat.factorial_ne_zero x) (Nat.factorial_ne_zero n)
    · exact Nat.factorial_dvd_factorial (by omega)
    · norm_cast; exact Nat.factorial_ne_zero x
  · simp only [coeff_mul_natCast, h, ↓reduceIte, mul_eq_zero, Nat.cast_eq_zero,
    Nat.div_eq_zero_iff]
    left
    by_cases hn : n = 0
    · simp only [hn, Nat.factorial_zero, Nat.cast_one, inv_one, coeff_C, h, ↓reduceIte]
    · simp only [coeff_C, h, ↓reduceIte]

/-- `shiftedLegendre n` is an integer polynomial. -/
lemma shiftedLegendre_eq_int_poly (n : ℕ) : ∃ a : ℕ → ℤ, shiftedLegendre n =
    ∑ k ∈ Finset.range (n + 1), (a k) • X ^ k := by
  simp_rw [shiftedLegendre_eq_sum]
  use fun k => (- 1) ^ k * (Nat.choose n k) * (Nat.choose (n + k) n)
  congr! 1 with x
  simp

/-- The values ​​of the Legendre polynomial at x and 1-x differ by a factor (-1)ⁿ. -/
lemma shiftedLegendre_eval_symm (n : ℕ) (x : ℝ) :
    eval x (shiftedLegendre n) = (-1) ^ n * eval (1 - x) (shiftedLegendre n) := by
  rw [mul_comm]
  simp only [shiftedLegendre, eval_mul, one_div, eval_C]
  rw [mul_assoc]
  simp only [mul_eq_mul_left_iff, inv_eq_zero, Nat.cast_eq_zero]; left
  rw [Polynomial.iterate_derivative_mul]
  simp only [Nat.succ_eq_add_one, nsmul_eq_mul]
  rw [Polynomial.eval_finset_sum, Polynomial.eval_finset_sum, ← Finset.sum_flip, Finset.sum_mul]
  congr! 1 with i hi
  simp only [Polynomial.iterate_derivative_X_pow_eq_smul, eval_mul, eval_natCast,
    Algebra.smul_mul_assoc, eval_smul, eval_mul, eval_pow, eval_X, smul_eq_mul]
  simp only [Finset.mem_range, Nat.lt_add_one_iff] at hi
  have hx : (1 - X : ℝ[X]) ^ n = (X ^ n : ℝ[X]).comp (1 - X) :=by simp
  rw [hx]
  simp only [Polynomial.iterate_derivative_comp_one_sub_X,
    Polynomial.iterate_derivative_X_pow_eq_smul, Algebra.smul_def, algebraMap_eq, map_natCast]
  rw [Nat.choose_symm hi]
  simp only [mul_comp, natCast_comp, pow_comp, X_comp, eval_mul, eval_pow, eval_neg, eval_one,
    eval_natCast, eval_sub, eval_X, sub_sub_cancel]
  rw [mul_assoc]
  simp only [mul_eq_mul_left_iff, Nat.cast_eq_zero]; left
  rw [show n - (n - i) = i by omega, ← mul_assoc, ← mul_assoc, mul_comm, ← mul_assoc]
  symm
  rw [← mul_assoc]
  nth_rewrite 4 [mul_comm]
  rw [← mul_assoc, ← mul_assoc, mul_assoc]
  congr 1
  rw [← pow_add, show i + n = n - i + 2 * i by omega, pow_add]
  simp only [even_two, Even.mul_right, Even.neg_pow, one_pow, mul_one]

end Polynomial
