/-
Copyright (c) 2025 Junqi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junqi Liu, Jinzhao Pan
-/
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Analysis.Normed.Ring.Lemmas

/-!
# shifted Legendre Polynomials

In this file, we define the shifted Legendre polynomials `shiftedLegendre n` for `n : ℕ` as a
polynomial in `ℤ[X]`. We prove some basic properties of the Legendre polynomials.

* `factorial_mul_shiftedLegendre_eq`: The analogue of Rodrigues' formula for the shifted Legendre
  polynomials;
* `shiftedLegendre_eval_symm`: The values of the shifted Legendre polynomial at `x` and `1 - x`
  differ by a factor `(-1)ⁿ`.

## Reference

* <https://en.wikipedia.org/wiki/Legendre_polynomials>

## Tags

shifted Legendre polynomials, derivative
-/

open scoped Nat
open BigOperators Finset

namespace Polynomial

/-- `shiftedLegendre n` is the polynomial defined as the sum of integer monomials. -/
noncomputable def shiftedLegendre (n : ℕ) : ℤ[X] :=
  ∑ k ∈ Finset.range (n + 1), C ((-1) ^ k * (Nat.choose n k) * (Nat.choose (n + k) n) : ℤ) * X ^ k

/-- The shifted Legendre polynomial multiplied by a factorial equals the higher-order derivative of
  the combinatorial function `X ^ n * (1 - X) ^ n`. This is the analogue of Rodrigues' formula for
  the shifted Legendre polynomials. -/
theorem factorial_mul_shiftedLegendre_eq (n : ℕ) : (n ! : ℤ[X]) * (shiftedLegendre n) =
    derivative^[n] (X ^ n * (1 - (X : ℤ[X])) ^ n) := by
  symm
  have h : ((X : ℤ[X]) - X ^ 2) ^ n =
      ∑ m ∈ range (n + 1), n.choose m • (- 1) ^ m * X ^ (n + m) := by
    rw [sub_eq_add_neg, add_comm, add_pow]
    congr! 1 with m hm
    rw [neg_pow, pow_two, mul_pow, ← mul_assoc, mul_comm, mul_assoc, pow_mul_pow_sub, mul_assoc,
      ← pow_add, ← mul_assoc, nsmul_eq_mul, add_comm]
    rw [Finset.mem_range] at hm
    linarith
  rw [shiftedLegendre, ← mul_pow, mul_one_sub, ← pow_two, h, iterate_derivative_sum,
    Finset.mul_sum]
  congr! 1 with x _
  rw [show (n.choose x • (-1) ^ x : ℤ[X]) = C (n.choose x • (-1) ^ x) by simp,
    iterate_derivative_C_mul, iterate_derivative_X_pow_eq_smul,
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

/-- The coefficient of the shifted Legendre polynomial at `k` is
  `(-1) ^ k * (n.choose k) * (n + k).choose n`. -/
theorem coeff_shiftedLegendre (n k : ℕ) :
    (shiftedLegendre n).coeff k = (-1) ^ k * (Nat.choose n k) * (Nat.choose (n + k) n) := by
  rw [shiftedLegendre, finset_sum_coeff]
  simp_rw [coeff_C_mul_X_pow]
  simp only [Int.reduceNeg, sum_ite_eq, mem_range, ite_eq_left_iff, not_lt, zero_eq_mul,
    mul_eq_zero, pow_eq_zero_iff', neg_eq_zero, one_ne_zero, ne_eq, false_and, Int.natCast_eq_zero,
    false_or]
  intro h
  simp [Nat.choose_eq_zero_of_lt h]

/-- The degree of `shiftedLegendre n` is `n`. -/
theorem degree_shiftedLegendre (n : ℕ) : (shiftedLegendre n).degree = n := by
  refine le_antisymm ?_ (le_degree_of_ne_zero ?_)
  · rw [degree_le_iff_coeff_zero]
    intro k h
    norm_cast at h
    simp [coeff_shiftedLegendre, Nat.choose_eq_zero_of_lt h]
  · simp [coeff_shiftedLegendre, (Nat.choose_pos (show n ≤ n + n by simp)).ne']

theorem natDegree_shiftedLegendre (n : ℕ) : (shiftedLegendre n).natDegree = n :=
  natDegree_eq_of_degree_eq_some (degree_shiftedLegendre n)

theorem neg_one_pow_mul_shiftedLegendre_comp_one_sub_X_eq (n : ℕ) :
    (-1) ^ n * (shiftedLegendre n).comp (1 - X) = shiftedLegendre n := by
  rw [← mul_right_inj' (a := (n ! : ℤ[X])) (by exact_mod_cast Nat.factorial_ne_zero n),
    ← mul_assoc, mul_comm (n ! : ℤ[X]), mul_assoc, ← natCast_mul_comp,
    factorial_mul_shiftedLegendre_eq, ← iterate_derivative_comp_one_sub_X]
  congr 1
  simp [mul_comm]

/-- The values ​​of the Legendre polynomial at `x` and `1 - x` differ by a factor `(-1)ⁿ`. -/
lemma shiftedLegendre_eval_symm (n : ℕ) {R : Type*} [Ring R] (x : R) :
    aeval x (shiftedLegendre n) = (-1) ^ n * aeval (1 - x) (shiftedLegendre n) := by
  have := congr(aeval x $(neg_one_pow_mul_shiftedLegendre_comp_one_sub_X_eq n))
  simpa [aeval_comp] using this.symm

end Polynomial
