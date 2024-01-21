/-
Copyright (c) 2022 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Mathlib.Data.Nat.Prime
import Mathlib.Data.Real.Archimedean

/-!
# The Lindemann-Weierstrass theorem
-/

open scoped Nat

theorem linear_independent_exp_exists_prime_nat' (c : ℕ) : ∃ n0, ∀ n ≥ n0, c ^ n < (n - 1)! := by
  obtain (rfl | c0) := c.eq_zero_or_pos
  · use 1
    intro n hn
    rw [zero_pow hn]
    exact Nat.factorial_pos _
  refine' ⟨2 * (c ^ 2 + 1), _⟩
  intro n hn
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
  refine (Nat.le_mul_of_pos_right _ (pow_pos c0 d)).trans_lt ?_
  convert_to (c ^ 2) ^ (c ^ 2 + d + 1) < (c ^ 2 + (c ^ 2 + d + 1))!
  · ring
  · congr; omega
  refine lt_of_lt_of_le ?_ Nat.factorial_mul_pow_le_factorial
  rw [← one_mul (_ ^ _ : ℕ)]
  exact Nat.mul_lt_mul_of_le_of_lt (Nat.one_le_of_lt (Nat.factorial_pos _))
    (Nat.pow_lt_pow_left (Nat.lt_succ_self _) (Nat.succ_ne_zero _)) (Nat.factorial_pos _)

theorem linear_independent_exp_exists_prime_nat (a : ℕ) (c : ℕ) :
    ∃ n0, ∀ n ≥ n0, a * c ^ n < (n - 1)! := by
  obtain ⟨n0, h⟩ := linear_independent_exp_exists_prime_nat' (a * c)
  use max n0 1
  intro n hn
  have n0_le_n := (le_max_left _ _).trans hn
  have one_le_n := (le_max_right _ _).trans hn
  specialize h n n0_le_n
  refine' lt_of_le_of_lt _ h
  obtain (rfl | a0) := a.eq_zero_or_pos
  · simp only [zero_mul, zero_le]
  rw [mul_pow]
  apply Nat.mul_le_mul_right
  apply le_self_pow <;> omega

theorem linear_independent_exp_exists_prime (n : ℕ) (a : ℝ) (c : ℝ) :
    ∃ p > n, p.Prime ∧ a * c ^ p / (p - 1)! < 1 := by
  simp_rw [@div_lt_one ℝ _ _ _ (Nat.cast_pos.mpr (Nat.factorial_pos _))]
  obtain ⟨n0, h⟩ := linear_independent_exp_exists_prime_nat ⌈|a|⌉.natAbs ⌈|c|⌉.natAbs
  obtain ⟨p, hp, prime_p⟩ := (max (n + 1) n0).exists_infinite_primes
  use p, (le_max_left _ _).trans hp, prime_p
  have : a * c ^ p ≤ ⌈|a|⌉ * (⌈|c|⌉ : ℝ) ^ p
  · refine' (le_abs_self _).trans _
    rw [_root_.abs_mul, _root_.abs_pow]
    refine'
      mul_le_mul (Int.le_ceil _) (pow_le_pow_left (abs_nonneg _) (Int.le_ceil _) _)
        (pow_nonneg (abs_nonneg _) _) (Int.cast_nonneg.mpr (Int.ceil_nonneg (abs_nonneg _)))
  refine' this.trans_lt _; clear this
  refine' lt_of_eq_of_lt (_ : _ = ((⌈|a|⌉.natAbs * ⌈|c|⌉.natAbs ^ p : ℕ) : ℝ)) _
  · simp_rw [Nat.cast_mul, Nat.cast_pow, Int.cast_natAbs,
      abs_eq_self.mpr (Int.ceil_nonneg (_root_.abs_nonneg (_ : ℝ)))]
  rw [Nat.cast_lt]
  exact h _ ((le_max_right _ _).trans hp)
#align linear_independent_exp_exists_prime linear_independent_exp_exists_prime
