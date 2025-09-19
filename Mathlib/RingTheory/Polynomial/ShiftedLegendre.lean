/-
Copyright (c) 2025 Junqi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junqi Liu, Jinzhao Pan
-/
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Derivative

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

open Nat BigOperators Finset

namespace Polynomial

/-- `shiftedLegendre n` is an integer polynomial for each `n : ℕ`, defined by:
`Pₙ(x) = ∑ k ∈ Finset.range (n + 1), (-1)ᵏ * choose n k * choose (n + k) n * xᵏ`
These polynomials appear in combinatorics and the theory of orthogonal polynomials. -/
noncomputable def shiftedLegendre (n : ℕ) : ℤ[X] :=
  ∑ k ∈ Finset.range (n + 1), C ((-1 : ℤ) ^ k * n.choose k * (n + k).choose n) * X ^ k

/-- The shifted Legendre polynomial multiplied by a factorial equals the higher-order derivative of
the combinatorial function `X ^ n * (1 - X) ^ n`. This is the analogue of Rodrigues' formula for
the shifted Legendre polynomials. -/
theorem factorial_mul_shiftedLegendre_eq (n : ℕ) : (n ! : ℤ[X]) * (shiftedLegendre n) =
    derivative^[n] (X ^ n * (1 - (X : ℤ[X])) ^ n) := by
  symm
  calc
  _ = derivative^[n] (((X : ℤ[X]) - X ^ 2) ^ n) := by
    rw [← mul_pow, mul_one_sub, ← pow_two]
  _ = derivative^[n] (∑ m ∈ range (n + 1), n.choose m • (-1) ^ m * X ^ (n + m)) := by
    congr
    rw [sub_eq_add_neg, add_comm, add_pow]
    congr! 1 with m hm
    rw [neg_pow, pow_two, mul_pow, ← mul_assoc, mul_comm, mul_assoc, pow_mul_pow_sub, mul_assoc,
      ← pow_add, ← mul_assoc, nsmul_eq_mul, add_comm]
    rw [Finset.mem_range] at hm
    linarith
  _ = ∑ x ∈ range (n + 1), ↑((n + x)! / x !) * C (↑(n.choose x) * (-1) ^ x) * X ^ x := by
    rw [iterate_derivative_sum]
    congr! 1 with x _
    rw [show (n.choose x • (-1) ^ x : ℤ[X]) = C (n.choose x • (-1) ^ x) by simp,
      iterate_derivative_C_mul, iterate_derivative_X_pow_eq_smul,
      descFactorial_eq_div (by cutsat), show n + x - n = x by cutsat]
    simp only [Int.reduceNeg, nsmul_eq_mul, eq_intCast, Int.cast_mul, Int.cast_natCast,
      Int.cast_pow, Int.cast_neg, Int.cast_one, zsmul_eq_mul]
    ring
  _ = ∑ i ∈ range (n + 1), ↑n ! * C ((-1) ^ i * ↑(n.choose i) * ↑((n + i).choose n)) * X ^ i := by
    congr! 2 with x _
    rw [C_mul (b := ((n + x).choose n : ℤ)), mul_comm, mul_comm (n ! : ℤ[X]), mul_comm _ ((-1) ^ x),
      mul_assoc]
    congr 1
    rw [add_comm, add_choose]
    simp only [Int.natCast_ediv, cast_mul, eq_intCast]
    norm_cast
    rw [mul_comm, ← Nat.mul_div_assoc]
    · rw [mul_comm, Nat.mul_div_mul_right _ _ (by positivity)]
    · simp only [factorial_mul_factorial_dvd_factorial_add]
  _ = (n ! : ℤ[X]) * (shiftedLegendre n) := by simp [← mul_assoc, shiftedLegendre, mul_sum]

/-- The coefficient of the shifted Legendre polynomial at `k` is
`(-1) ^ k * (n.choose k) * (n + k).choose n`. -/
theorem coeff_shiftedLegendre (n k : ℕ) :
    (shiftedLegendre n).coeff k = (-1) ^ k * n.choose k * (n + k).choose n := by
  rw [shiftedLegendre, finset_sum_coeff]
  simp_rw [coeff_C_mul_X_pow]
  simp +contextual [choose_eq_zero_of_lt, add_one_le_iff]

/-- The degree of `shiftedLegendre n` is `n`. -/
@[simp] theorem degree_shiftedLegendre (n : ℕ) : (shiftedLegendre n).degree = n := by
  refine le_antisymm ?_ (le_degree_of_ne_zero ?_)
  · rw [degree_le_iff_coeff_zero]
    intro k h
    norm_cast at h
    simp [coeff_shiftedLegendre, choose_eq_zero_of_lt h]
  · simp [coeff_shiftedLegendre, (choose_pos (show n ≤ n + n by simp)).ne']

@[simp] theorem natDegree_shiftedLegendre (n : ℕ) : (shiftedLegendre n).natDegree = n :=
  natDegree_eq_of_degree_eq_some (degree_shiftedLegendre n)

theorem neg_one_pow_mul_shiftedLegendre_comp_one_sub_X_eq (n : ℕ) :
    (-1) ^ n * (shiftedLegendre n).comp (1 - X) = shiftedLegendre n := by
  refine nat_mul_inj' ?_ (factorial_ne_zero n)
  rw [← mul_assoc, mul_comm (n ! : ℤ[X]), mul_assoc, ← natCast_mul_comp,
    factorial_mul_shiftedLegendre_eq, ← iterate_derivative_comp_one_sub_X]
  simp [mul_comm]

/-- The values ​​of the Legendre polynomial at `x` and `1 - x` differ by a factor `(-1)ⁿ`. -/
lemma shiftedLegendre_eval_symm (n : ℕ) {R : Type*} [Ring R] (x : R) :
    aeval x (shiftedLegendre n) = (-1) ^ n * aeval (1 - x) (shiftedLegendre n) := by
  have := congr(aeval x $(neg_one_pow_mul_shiftedLegendre_comp_one_sub_X_eq n))
  simpa [aeval_comp] using this.symm

end Polynomial
