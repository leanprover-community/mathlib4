/-
Copyright (c) 2025 Junqi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junqi Liu
-/
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Analysis.RCLike.Basic

/-!
# shifted Legendre Polynomials

In this file, we define the shifted Legendre polynomials `shiftedLegendre n` for `n : ℕ` as a
polynomial in `ℤ[X]`. We prove some basic properties of the Legendre polynomials.
-/

open scoped Nat
open BigOperators Finset

variable {R : Type*}

namespace Polynomial

/-- `shiftedLegendre n` is the polynomial defined as the sum of integer monomials. -/
noncomputable def shiftedLegendre (n : ℕ) : ℤ[X] :=
  ∑ k ∈ Finset.range (n + 1), C ((-1) ^ k * (Nat.choose n k) * (Nat.choose (n + k) n) : ℤ) * X ^ k

/-- The expand of `shiftedLegendre n`. -/
theorem shiftedLegendre_eq_sum (n : ℕ) : (n ! : ℤ[X]) * (shiftedLegendre n) =
   derivative^[n] (X ^ n * (1 - (X : ℤ[X])) ^ n) := by
  symm
  have h : ((X : ℤ[X]) - X ^ 2) ^ n =
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
  rw [show (n.choose x • (-1) ^ x : ℤ[X]) = C (n.choose x • (-1) ^ x) by simp,
    Polynomial.iterate_derivative_C_mul, Polynomial.iterate_derivative_X_pow_eq_smul,
    Nat.descFactorial_eq_div (by omega), show n + x - n = x by omega, nsmul_eq_mul,
    ← mul_assoc, mul_assoc, mul_comm]
  simp only [map_mul, map_natCast, map_pow, map_neg, map_one, Algebra.mul_smul_comm,
    Algebra.smul_mul_assoc, X_pow_mul_assoc_C]
  rw [Algebra.smul_def, algebraMap_eq, map_natCast, add_comm, Nat.add_choose, ← mul_assoc,
    ← mul_assoc, ← mul_assoc, mul_rotate, ← mul_assoc, ← mul_assoc]
  congr 1
  nth_rw 2 [mul_rotate, mul_assoc, mul_comm]
  congr 1
  simp only [mul_comm, ← Nat.cast_mul, Nat.cast_inj]
  rw [Nat.div_eq_iff_eq_mul_left (by positivity)]
  · rw [mul_comm, ← mul_assoc, mul_comm (x !), ← Nat.mul_div_assoc]
    · rw [Nat.mul_div_cancel_left _ (by positivity)]
    · simp only [add_comm, Nat.factorial_mul_factorial_dvd_factorial_add]
  · exact Nat.factorial_dvd_factorial (by omega)

/-- `shiftedLegendre n` is an integer polynomial. -/
lemma shiftedLegendre_eq_int_poly (n : ℕ) : ∃ a : ℕ → ℤ, shiftedLegendre n =
    ∑ k ∈ Finset.range (n + 1), (a k) • X ^ k := by
  use fun k => (- 1) ^ k * (Nat.choose n k) * (Nat.choose (n + k) n)
  simp only [shiftedLegendre, Int.reduceNeg, eq_intCast, Int.cast_mul, Int.cast_pow, Int.cast_neg,
    Int.cast_one, Int.cast_natCast, zsmul_eq_mul]

/-- The values ​​of the Legendre polynomial at `x` and `1 - x` differ by a factor `(-1)ⁿ`. -/
lemma shiftedLegendre_eval_symm (n : ℕ) (x : ℝ) :
    aeval x (shiftedLegendre n) = (-1) ^ n * aeval (1 - x) (shiftedLegendre n) := by
  rw [mul_comm, ← mul_right_inj' (a := (aeval x) (n ! : ℤ[X])) (by simp; positivity), ← mul_assoc,
    ← aeval_mul, show (aeval x) (n ! : ℤ[X]) = (aeval (1 - x)) (n ! : ℤ[X]) by simp, ← aeval_mul]
  simp only [shiftedLegendre_eq_sum]
  rw [Polynomial.iterate_derivative_mul]
  simp only [Nat.succ_eq_add_one, nsmul_eq_mul, map_sum, map_mul, map_natCast]
  rw [← Finset.sum_flip, Finset.sum_mul]
  congr! 1 with i hi
  simp only [iterate_derivative_X_pow_eq_smul, zsmul_eq_mul, Int.cast_natCast, map_mul, map_natCast,
    map_pow, aeval_X]
  simp only [Finset.mem_range, Nat.lt_add_one_iff] at hi
  have hx : (1 - X : ℤ[X]) ^ n = (X ^ n : ℤ[X]).comp (1 - X) := by simp only [pow_comp, X_comp]
  rw [hx]
  simp only [Polynomial.iterate_derivative_comp_one_sub_X,
    Polynomial.iterate_derivative_X_pow_eq_smul, Algebra.smul_def, algebraMap_eq, map_natCast]
  rw [Nat.choose_symm hi]
  simp only [mul_comp, natCast_comp, pow_comp, X_comp, map_mul, map_pow, map_neg, map_one,
    map_natCast, map_sub, aeval_X, sub_sub_cancel]
  rw [show n - (n - i) = i by omega]
  ring_nf
  rw [mul_assoc (b := (-1) ^ i)]
  congr 2
  rw [← pow_add, show i + n = n - i + 2 * i by omega, pow_add]
  simp only [even_two, Even.mul_right, Even.neg_pow, one_pow, mul_one]

end Polynomial
