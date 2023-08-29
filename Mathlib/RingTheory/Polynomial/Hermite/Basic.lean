/-
Copyright (c) 2023 Luke Mantle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Mantle
-/
import Mathlib.Data.Polynomial.Derivative
import Mathlib.Data.Nat.Parity
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
  -- 🎉 no goals
#align polynomial.hermite_succ Polynomial.hermite_succ

theorem hermite_eq_iterate (n : ℕ) : hermite n = (fun p => X * p - derivative p)^[n] 1 := by
  induction' n with n ih
  -- ⊢ hermite Nat.zero = (fun p => X * p - ↑derivative p)^[Nat.zero] 1
  · rfl
    -- 🎉 no goals
  · rw [Function.iterate_succ_apply', ← ih, hermite_succ]
    -- 🎉 no goals
#align polynomial.hermite_eq_iterate Polynomial.hermite_eq_iterate

@[simp]
theorem hermite_zero : hermite 0 = C 1 :=
  rfl
#align polynomial.hermite_zero Polynomial.hermite_zero

-- Porting note: There was initially @[simp] on this line but it was removed
-- because simp can prove this theorem
theorem hermite_one : hermite 1 = X := by
  rw [hermite_succ, hermite_zero]
  -- ⊢ X * ↑C 1 - ↑derivative (↑C 1) = X
  simp only [map_one, mul_one, derivative_one, sub_zero]
  -- 🎉 no goals
#align polynomial.hermite_one Polynomial.hermite_one

/-! ### Lemmas about `Polynomial.coeff` -/


section coeff

theorem coeff_hermite_succ_zero (n : ℕ) : coeff (hermite (n + 1)) 0 = -coeff (hermite n) 1 := by
  simp [coeff_derivative]
  -- 🎉 no goals
#align polynomial.coeff_hermite_succ_zero Polynomial.coeff_hermite_succ_zero

theorem coeff_hermite_succ_succ (n k : ℕ) : coeff (hermite (n + 1)) (k + 1) =
    coeff (hermite n) k - (k + 2) * coeff (hermite n) (k + 2) := by
  rw [hermite_succ, coeff_sub, coeff_X_mul, coeff_derivative, mul_comm]
  -- ⊢ coeff (hermite n) k - (↑(k + 1) + 1) * coeff (hermite n) (k + 1 + 1) = coeff …
  norm_cast
  -- 🎉 no goals
#align polynomial.coeff_hermite_succ_succ Polynomial.coeff_hermite_succ_succ

theorem coeff_hermite_of_lt {n k : ℕ} (hnk : n < k) : coeff (hermite n) k = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hnk
  -- ⊢ coeff (hermite n) (n + k + 1) = 0
  clear hnk
  -- ⊢ coeff (hermite n) (n + k + 1) = 0
  induction' n with n ih generalizing k
  -- ⊢ coeff (hermite Nat.zero) (Nat.zero + k + 1) = 0
  · apply coeff_C
    -- 🎉 no goals
  · have : n + k + 1 + 2 = n + (k + 2) + 1 := by ring
    -- ⊢ coeff (hermite (Nat.succ n)) (Nat.succ n + k + 1) = 0
    rw [Nat.succ_eq_add_one, coeff_hermite_succ_succ, add_right_comm, this, ih k, ih (k + 2),
      mul_zero, sub_zero]
#align polynomial.coeff_hermite_of_lt Polynomial.coeff_hermite_of_lt

@[simp]
theorem coeff_hermite_self (n : ℕ) : coeff (hermite n) n = 1 := by
  induction' n with n ih
  -- ⊢ coeff (hermite Nat.zero) Nat.zero = 1
  · apply coeff_C
    -- 🎉 no goals
  · rw [coeff_hermite_succ_succ, ih, coeff_hermite_of_lt, mul_zero, sub_zero]
    -- ⊢ n < n + 2
    simp
    -- 🎉 no goals
#align polynomial.coeff_hermite_self Polynomial.coeff_hermite_self

@[simp]
theorem degree_hermite (n : ℕ) : (hermite n).degree = n := by
  rw [degree_eq_of_le_of_coeff_ne_zero]
  -- ⊢ degree (hermite n) ≤ ↑n
  simp_rw [degree_le_iff_coeff_zero, Nat.cast_lt]
  -- ⊢ ∀ (m : ℕ), n < m → coeff (hermite n) m = 0
  · rintro m hnm
    -- ⊢ coeff (hermite n) m = 0
    exact coeff_hermite_of_lt hnm
    -- 🎉 no goals
  · simp [coeff_hermite_self n]
    -- 🎉 no goals
#align polynomial.degree_hermite Polynomial.degree_hermite

@[simp]
theorem natDegree_hermite {n : ℕ} : (hermite n).natDegree = n :=
  natDegree_eq_of_degree_eq_some (degree_hermite n)
#align polynomial.nat_degree_hermite Polynomial.natDegree_hermite

@[simp]
theorem leadingCoeff_hermite (n : ℕ) : (hermite n).leadingCoeff = 1 := by
  rw [← coeff_natDegree, natDegree_hermite, coeff_hermite_self]
  -- 🎉 no goals
#align polynomial.leading_coeff_hermite Polynomial.leadingCoeff_hermite

theorem hermite_monic (n : ℕ) : (hermite n).Monic :=
  leadingCoeff_hermite n
#align polynomial.hermite_monic Polynomial.hermite_monic

theorem coeff_hermite_of_odd_add {n k : ℕ} (hnk : Odd (n + k)) : coeff (hermite n) k = 0 := by
  induction' n with n ih generalizing k
  -- ⊢ coeff (hermite Nat.zero) k = 0
  · rw [Nat.zero_eq, zero_add k] at hnk
    -- ⊢ coeff (hermite Nat.zero) k = 0
    exact coeff_hermite_of_lt hnk.pos
    -- 🎉 no goals
  · cases' k with k
    -- ⊢ coeff (hermite (Nat.succ n)) Nat.zero = 0
    · rw [Nat.succ_add_eq_succ_add] at hnk
      -- ⊢ coeff (hermite (Nat.succ n)) Nat.zero = 0
      rw [coeff_hermite_succ_zero, ih hnk, neg_zero]
      -- 🎉 no goals
    · rw [coeff_hermite_succ_succ, ih, ih, mul_zero, sub_zero]
      -- ⊢ Odd (n + (k + 2))
      · rwa [Nat.succ_add_eq_succ_add] at hnk
        -- 🎉 no goals
      · rw [(by rw [Nat.succ_add, Nat.add_succ] : n.succ + k.succ = n + k + 2)] at hnk
        -- ⊢ Odd (n + k)
        exact (Nat.odd_add.mp hnk).mpr even_two
        -- 🎉 no goals
#align polynomial.coeff_hermite_of_odd_add Polynomial.coeff_hermite_of_odd_add

end coeff

section CoeffExplicit

open scoped Nat

/-- Because of `coeff_hermite_of_odd_add`, every nonzero coefficient is described as follows. -/
theorem coeff_hermite_explicit :
    ∀ n k : ℕ, coeff (hermite (2 * n + k)) k = (-1) ^ n * (2 * n - 1)‼ * Nat.choose (2 * n + k) k
  | 0, _ => by simp
               -- 🎉 no goals
  | n + 1, 0 => by
    convert coeff_hermite_succ_zero (2 * n + 1) using 1
    -- ⊢ (-1) ^ (n + 1) * ↑(2 * (n + 1) - 1)‼ * ↑(Nat.choose (2 * (n + 1) + 0) 0) = - …
    -- porting note: ring_nf did not solve the goal on line 165
    rw [coeff_hermite_explicit n 1, (by rw [Nat.left_distrib, mul_one, Nat.succ_sub_one] :
      2 * (n + 1) - 1 = 2 * n + 1), Nat.doubleFactorial_add_one, Nat.choose_zero_right,
      Nat.choose_one_right, pow_succ]
    push_cast
    -- ⊢ -1 * (-1) ^ n * ((2 * ↑n + 1) * ↑(2 * n - 1)‼) * 1 = -((-1) ^ n * ↑(2 * n -  …
    ring
    -- 🎉 no goals
  | n + 1, k + 1 => by
    let hermite_explicit : ℕ → ℕ → ℤ := fun n k =>
      (-1) ^ n * (2 * n - 1)‼ * Nat.choose (2 * n + k) k
    have hermite_explicit_recur :
      ∀ n k : ℕ,
        hermite_explicit (n + 1) (k + 1) =
          hermite_explicit (n + 1) k - (k + 2) * hermite_explicit n (k + 2) := by
      intro n k
      simp only
      -- Factor out (-1)'s.
      rw [mul_comm (↑k + _ : ℤ), sub_eq_add_neg]
      nth_rw 3 [neg_eq_neg_one_mul]
      simp only [mul_assoc, ← mul_add, pow_succ]
      congr 2
      -- Factor out double factorials.
      norm_cast
      -- porting note: ring_nf did not solve the goal on line 186
      rw [(by rw [Nat.left_distrib, mul_one, Nat.succ_sub_one] : 2 * (n + 1) - 1 = 2 * n + 1),
        Nat.doubleFactorial_add_one, mul_comm (2 * n + 1)]
      simp only [mul_assoc, ← mul_add]
      congr 1
      -- Match up binomial coefficients using `Nat.choose_succ_right_eq`.
      rw [(by ring : 2 * (n + 1) + (k + 1) = 2 * n + 1 + (k + 1) + 1),
        (by ring : 2 * (n + 1) + k = 2 * n + 1 + (k + 1)),
        (by ring : 2 * n + (k + 2) = 2 * n + 1 + (k + 1))]
      rw [Nat.choose, Nat.choose_succ_right_eq (2 * n + 1 + (k + 1)) (k + 1), Nat.add_sub_cancel,
        Int.negSucc_eq]
      -- porting note: ring could not solve the goal so the lines 195, 198-200 were added.
      ring_nf
      simp only [sub_eq_add_neg, ← neg_mul, ← right_distrib _ _ ((-(1 : ℤ)) ^ n), ← neg_add]
      norm_cast
      simp only [← add_assoc, add_comm]
    change _ = hermite_explicit _ _
    -- ⊢ coeff (hermite (2 * (n + 1) + (k + 1))) (k + 1) = hermite_explicit (n + 1) ( …
    rw [← add_assoc, coeff_hermite_succ_succ, hermite_explicit_recur]
    -- ⊢ coeff (hermite (2 * (n + 1) + k)) k - (↑k + 2) * coeff (hermite (2 * (n + 1) …
    congr
    -- ⊢ coeff (hermite (2 * (n + 1) + k)) k = hermite_explicit (n + 1) k
    · rw [coeff_hermite_explicit (n + 1) k]
      -- 🎉 no goals
    · rw [(by ring : 2 * (n + 1) + k = 2 * n + (k + 2)), coeff_hermite_explicit n (k + 2)]
      -- 🎉 no goals
-- porting note: Lean 3 worked this out automatically
termination_by _ n k => (n, k)
#align polynomial.coeff_hermite_explicit Polynomial.coeff_hermite_explicit

theorem coeff_hermite_of_even_add {n k : ℕ} (hnk : Even (n + k)) :
    coeff (hermite n) k = (-1) ^ ((n - k) / 2) * (n - k - 1)‼ * Nat.choose n k := by
  cases' le_or_lt k n with h_le h_lt
  -- ⊢ coeff (hermite n) k = (-1) ^ ((n - k) / 2) * ↑(n - k - 1)‼ * ↑(Nat.choose n k)
  · rw [Nat.even_add, ← Nat.even_sub h_le] at hnk
    -- ⊢ coeff (hermite n) k = (-1) ^ ((n - k) / 2) * ↑(n - k - 1)‼ * ↑(Nat.choose n k)
    obtain ⟨m, hm⟩ := hnk
    -- ⊢ coeff (hermite n) k = (-1) ^ ((n - k) / 2) * ↑(n - k - 1)‼ * ↑(Nat.choose n k)
    -- porting note: linarith failed to find a contradiction by itself
    rw [(by linarith [by rwa [Nat.sub_eq_iff_eq_add h_le] at hm] : n = 2 * m + k),
      Nat.add_sub_cancel, Nat.mul_div_cancel_left _ (Nat.succ_pos 1), coeff_hermite_explicit]
  · simp [Nat.choose_eq_zero_of_lt h_lt, coeff_hermite_of_lt h_lt]
    -- 🎉 no goals
#align polynomial.coeff_hermite_of_even_add Polynomial.coeff_hermite_of_even_add

theorem coeff_hermite (n k : ℕ) :
    coeff (hermite n) k =
      if Even (n + k) then (-1 : ℤ) ^ ((n - k) / 2) * (n - k - 1)‼ * Nat.choose n k else 0 := by
  split_ifs with h
  -- ⊢ coeff (hermite n) k = (-1) ^ ((n - k) / 2) * ↑(n - k - 1)‼ * ↑(Nat.choose n k)
  exact coeff_hermite_of_even_add h
  -- ⊢ coeff (hermite n) k = 0
  exact coeff_hermite_of_odd_add (Nat.odd_iff_not_even.mpr h)
  -- 🎉 no goals
#align polynomial.coeff_hermite Polynomial.coeff_hermite

end CoeffExplicit

end Polynomial
