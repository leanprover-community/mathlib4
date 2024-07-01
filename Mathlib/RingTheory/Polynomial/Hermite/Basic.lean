/-
Copyright (c) 2023 Luke Mantle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Mantle
-/
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Data.Nat.Factorial.DoubleFactorial

#align_import ring_theory.polynomial.hermite.basic from "leanprover-community/mathlib"@"938d3db9c278f8a52c0f964a405806f0f2b09b74"

/-!
# Hermite polynomials

This file defines `Polynomial.hermite n`, the `n`th probabilists' Hermite polynomial.

## Main definitions

* `Polynomial.hermite n`: the `n`th probabilists' Hermite polynomial,
  defined recursively as a `Polynomial ℤ`

## Results

* `Polynomial.hermite_succ`: the recursion `hermite (n+1) = (x - d/dx) (hermite n)`
* `Polynomial.coeff_hermite_explicit`: a closed formula for (nonvanishing) coefficients in terms
  of binomial coefficients and double factorials.
* `Polynomial.coeff_hermite_of_odd_add`: for `n`,`k` where `n+k` is odd, `(hermite n).coeff k` is
  zero.
* `Polynomial.coeff_hermite_of_even_add`: a closed formula for `(hermite n).coeff k` when `n+k` is
  even, equivalent to `Polynomial.coeff_hermite_explicit`.
* `Polynomial.monic_hermite`: for all `n`, `hermite n` is monic.
* `Polynomial.degree_hermite`: for all `n`, `hermite n` has degree `n`.

## References

* [Hermite Polynomials](https://en.wikipedia.org/wiki/Hermite_polynomials)

-/


noncomputable section

open Polynomial

namespace Polynomial

/-- the probabilists' Hermite polynomials. -/
noncomputable def hermite : ℕ → Polynomial ℤ
  | 0 => 1
  | n + 1 => X * hermite n - derivative (hermite n)
#align polynomial.hermite Polynomial.hermite

/-- The recursion `hermite (n+1) = (x - d/dx) (hermite n)` -/
@[simp]
theorem hermite_succ (n : ℕ) : hermite (n + 1) = X * hermite n - derivative (hermite n) := by
  rw [hermite]
#align polynomial.hermite_succ Polynomial.hermite_succ

theorem hermite_eq_iterate (n : ℕ) : hermite n = (fun p => X * p - derivative p)^[n] 1 := by
  induction' n with n ih
  · rfl
  · rw [Function.iterate_succ_apply', ← ih, hermite_succ]
#align polynomial.hermite_eq_iterate Polynomial.hermite_eq_iterate

@[simp]
theorem hermite_zero : hermite 0 = C 1 :=
  rfl
#align polynomial.hermite_zero Polynomial.hermite_zero

-- Porting note (#10618): There was initially @[simp] on this line but it was removed
-- because simp can prove this theorem
theorem hermite_one : hermite 1 = X := by
  rw [hermite_succ, hermite_zero]
  simp only [map_one, mul_one, derivative_one, sub_zero]
#align polynomial.hermite_one Polynomial.hermite_one

/-! ### Lemmas about `Polynomial.coeff` -/


section coeff

theorem coeff_hermite_succ_zero (n : ℕ) : coeff (hermite (n + 1)) 0 = -coeff (hermite n) 1 := by
  simp [coeff_derivative]
#align polynomial.coeff_hermite_succ_zero Polynomial.coeff_hermite_succ_zero

theorem coeff_hermite_succ_succ (n k : ℕ) : coeff (hermite (n + 1)) (k + 1) =
    coeff (hermite n) k - (k + 2) * coeff (hermite n) (k + 2) := by
  rw [hermite_succ, coeff_sub, coeff_X_mul, coeff_derivative, mul_comm]
  norm_cast
#align polynomial.coeff_hermite_succ_succ Polynomial.coeff_hermite_succ_succ

theorem coeff_hermite_of_lt {n k : ℕ} (hnk : n < k) : coeff (hermite n) k = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hnk
  clear hnk
  induction' n with n ih generalizing k
  · apply coeff_C
  · have : n + k + 1 + 2 = n + (k + 2) + 1 := by ring
    rw [coeff_hermite_succ_succ, add_right_comm, this, ih k, ih (k + 2),
      mul_zero, sub_zero]
#align polynomial.coeff_hermite_of_lt Polynomial.coeff_hermite_of_lt

@[simp]
theorem coeff_hermite_self (n : ℕ) : coeff (hermite n) n = 1 := by
  induction' n with n ih
  · apply coeff_C
  · rw [coeff_hermite_succ_succ, ih, coeff_hermite_of_lt, mul_zero, sub_zero]
    simp
#align polynomial.coeff_hermite_self Polynomial.coeff_hermite_self

@[simp]
theorem degree_hermite (n : ℕ) : (hermite n).degree = n := by
  rw [degree_eq_of_le_of_coeff_ne_zero]
  · simp_rw [degree_le_iff_coeff_zero, Nat.cast_lt]
    rintro m hnm
    exact coeff_hermite_of_lt hnm
  · simp [coeff_hermite_self n]
#align polynomial.degree_hermite Polynomial.degree_hermite

@[simp]
theorem natDegree_hermite {n : ℕ} : (hermite n).natDegree = n :=
  natDegree_eq_of_degree_eq_some (degree_hermite n)
#align polynomial.nat_degree_hermite Polynomial.natDegree_hermite

@[simp]
theorem leadingCoeff_hermite (n : ℕ) : (hermite n).leadingCoeff = 1 := by
  rw [← coeff_natDegree, natDegree_hermite, coeff_hermite_self]
#align polynomial.leading_coeff_hermite Polynomial.leadingCoeff_hermite

theorem hermite_monic (n : ℕ) : (hermite n).Monic :=
  leadingCoeff_hermite n
#align polynomial.hermite_monic Polynomial.hermite_monic

theorem coeff_hermite_of_odd_add {n k : ℕ} (hnk : Odd (n + k)) : coeff (hermite n) k = 0 := by
  induction' n with n ih generalizing k
  · rw [zero_add k] at hnk
    exact coeff_hermite_of_lt hnk.pos
  · cases' k with k
    · rw [Nat.succ_add_eq_add_succ] at hnk
      rw [coeff_hermite_succ_zero, ih hnk, neg_zero]
    · rw [coeff_hermite_succ_succ, ih, ih, mul_zero, sub_zero]
      · rwa [Nat.succ_add_eq_add_succ] at hnk
      · rw [(by rw [Nat.succ_add, Nat.add_succ] : n.succ + k.succ = n + k + 2)] at hnk
        exact (Nat.odd_add.mp hnk).mpr even_two
#align polynomial.coeff_hermite_of_odd_add Polynomial.coeff_hermite_of_odd_add

end coeff

section CoeffExplicit

open scoped Nat

/-- Because of `coeff_hermite_of_odd_add`, every nonzero coefficient is described as follows. -/
theorem coeff_hermite_explicit :
    ∀ n k : ℕ, coeff (hermite (2 * n + k)) k = (-1) ^ n * (2 * n - 1)‼ * Nat.choose (2 * n + k) k
  | 0, _ => by simp
  | n + 1, 0 => by
    convert coeff_hermite_succ_zero (2 * n + 1) using 1
    -- Porting note: ring_nf did not solve the goal on line 165
    rw [coeff_hermite_explicit n 1, (by rw [Nat.left_distrib, mul_one, Nat.add_one_sub_one] :
      2 * (n + 1) - 1 = 2 * n + 1), Nat.doubleFactorial_add_one, Nat.choose_zero_right,
      Nat.choose_one_right, pow_succ]
    push_cast
    ring
  | n + 1, k + 1 => by
    let hermite_explicit : ℕ → ℕ → ℤ := fun n k =>
      (-1) ^ n * (2 * n - 1)‼ * Nat.choose (2 * n + k) k
    have hermite_explicit_recur :
      ∀ n k : ℕ,
        hermite_explicit (n + 1) (k + 1) =
          hermite_explicit (n + 1) k - (k + 2) * hermite_explicit n (k + 2) := by
      intro n k
      simp only [hermite_explicit]
      -- Factor out (-1)'s.
      rw [mul_comm (↑k + _ : ℤ), sub_eq_add_neg]
      nth_rw 3 [neg_eq_neg_one_mul]
      simp only [mul_assoc, ← mul_add, pow_succ']
      congr 2
      -- Factor out double factorials.
      norm_cast
      -- Porting note: ring_nf did not solve the goal on line 186
      rw [(by rw [Nat.left_distrib, mul_one, Nat.add_one_sub_one] : 2 * (n + 1) - 1 = 2 * n + 1),
        Nat.doubleFactorial_add_one, mul_comm (2 * n + 1)]
      simp only [mul_assoc, ← mul_add]
      congr 1
      -- Match up binomial coefficients using `Nat.choose_succ_right_eq`.
      rw [(by ring : 2 * (n + 1) + (k + 1) = 2 * n + 1 + (k + 1) + 1),
        (by ring : 2 * (n + 1) + k = 2 * n + 1 + (k + 1)),
        (by ring : 2 * n + (k + 2) = 2 * n + 1 + (k + 1))]
      rw [Nat.choose, Nat.choose_succ_right_eq (2 * n + 1 + (k + 1)) (k + 1), Nat.add_sub_cancel]
      ring
    change _ = hermite_explicit _ _
    rw [← add_assoc, coeff_hermite_succ_succ, hermite_explicit_recur]
    congr
    · rw [coeff_hermite_explicit (n + 1) k]
    · rw [(by ring : 2 * (n + 1) + k = 2 * n + (k + 2)), coeff_hermite_explicit n (k + 2)]
#align polynomial.coeff_hermite_explicit Polynomial.coeff_hermite_explicit

theorem coeff_hermite_of_even_add {n k : ℕ} (hnk : Even (n + k)) :
    coeff (hermite n) k = (-1) ^ ((n - k) / 2) * (n - k - 1)‼ * Nat.choose n k := by
  rcases le_or_lt k n with h_le | h_lt
  · rw [Nat.even_add, ← Nat.even_sub h_le] at hnk
    obtain ⟨m, hm⟩ := hnk
    -- Porting note: linarith failed to find a contradiction by itself
    rw [(by omega : n = 2 * m + k),
      Nat.add_sub_cancel, Nat.mul_div_cancel_left _ (Nat.succ_pos 1), coeff_hermite_explicit]
  · simp [Nat.choose_eq_zero_of_lt h_lt, coeff_hermite_of_lt h_lt]
#align polynomial.coeff_hermite_of_even_add Polynomial.coeff_hermite_of_even_add

theorem coeff_hermite (n k : ℕ) :
    coeff (hermite n) k =
      if Even (n + k) then (-1 : ℤ) ^ ((n - k) / 2) * (n - k - 1)‼ * Nat.choose n k else 0 := by
  split_ifs with h
  · exact coeff_hermite_of_even_add h
  · exact coeff_hermite_of_odd_add (Nat.odd_iff_not_even.mpr h)
#align polynomial.coeff_hermite Polynomial.coeff_hermite

end CoeffExplicit

end Polynomial
