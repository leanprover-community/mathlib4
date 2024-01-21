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

theorem linear_independent_exp_exists_prime_nat'' (c : ℕ) : ∃ n > c, c ^ n < (n - 1)! := by
  refine' ⟨2 * (c ^ 2 + 1), _, _⟩; · have : c ≤ c * c := Nat.le_mul_self _; linarith
  rw [pow_mul, two_mul, add_right_comm, add_tsub_cancel_right]
  refine' lt_of_lt_of_le _ Nat.factorial_mul_pow_le_factorial
  rw [← one_mul (_ ^ _ : ℕ)]
  exact Nat.mul_lt_mul_of_le_of_lt (Nat.one_le_of_lt (Nat.factorial_pos _))
    (Nat.pow_lt_pow_left (Nat.lt_succ_self _) (Nat.succ_ne_zero _)) (Nat.factorial_pos _)
#align linear_independent_exp_exists_prime_nat'' linear_independent_exp_exists_prime_nat''

theorem linear_independent_exp_exists_prime_nat' (n : ℕ) (c : ℕ) :
    ∃ p > n, p.Prime ∧ c ^ p < (p - 1)! := by
  obtain ⟨m, hm, h⟩ := linear_independent_exp_exists_prime_nat'' c
  let N := max (n + 2) (m + 1)
  obtain ⟨p, hp', prime_p⟩ := Nat.exists_infinite_primes N
  have hnp : n + 1 < p := (Nat.add_one_le_iff.mp (le_max_left _ _)).trans_le hp'
  have hnp' : n < p := lt_of_add_lt_of_nonneg_left hnp zero_le_one
  have hmp : m < p := (Nat.add_one_le_iff.mp (le_max_right _ _)).trans_le hp'
  use p, hnp', prime_p
  cases' lt_or_ge m 2 with m2 m2
  · have : c = 0 := by linarith
    rw [this, zero_pow prime_p.pos]
    exact Nat.factorial_pos _
  rcases Nat.eq_zero_or_pos c with (rfl | c0)
  · rw [zero_pow prime_p.pos]
    exact Nat.factorial_pos _
  have m1 : 1 ≤ m := one_le_two.trans m2
  have one_le_m_sub_one : 1 ≤ m - 1 := by rwa [Nat.le_sub_iff_add_le m1]
  have : m - 1 - 1 < p - 1
  · rw [tsub_lt_tsub_iff_right one_le_m_sub_one]
    exact tsub_le_self.trans_lt hmp
  refine' lt_of_lt_of_le _ (Nat.factorial_mul_pow_sub_le_factorial this)
  have : (m - 1 - 1).succ = m - 1 := by rwa [Nat.succ_eq_add_one, tsub_add_cancel_of_le]
  rw [this]
  convert_to c ^ m * c ^ (p - m) < _
  · rw [← pow_add, add_tsub_cancel_of_le]; exact hmp.le
  rw [tsub_tsub_tsub_cancel_right m1]
  exact Nat.mul_lt_mul_of_lt_of_le' h (pow_le_pow_left' (Nat.le_pred_of_lt hm) _) (pow_pos c0 _)
#align linear_independent_exp_exists_prime_nat' linear_independent_exp_exists_prime_nat'

theorem linear_independent_exp_exists_prime_nat (n : ℕ) (a : ℕ) (c : ℕ) :
    ∃ p > n, p.Prime ∧ a * c ^ p < (p - 1)! := by
  obtain ⟨p, hp, prime_p, h⟩ := linear_independent_exp_exists_prime_nat' n (a * c)
  use p, hp, prime_p
  refine' lt_of_le_of_lt _ h
  rcases Nat.eq_zero_or_pos a with (rfl | a0)
  · simp_rw [MulZeroClass.zero_mul, zero_pow' _ prime_p.ne_zero, le_rfl]
  rw [mul_pow]
  apply Nat.mul_le_mul_right
  convert_to a ^ 1 ≤ a ^ p; · rw [pow_one]
  exact Nat.pow_le_pow_of_le_right a0 (Nat.one_le_of_lt prime_p.pos)
#align linear_independent_exp_exists_prime_nat linear_independent_exp_exists_prime_nat

theorem linear_independent_exp_exists_prime (n : ℕ) (a : ℝ) (c : ℝ) :
    ∃ p > n, p.Prime ∧ a * c ^ p / (p - 1)! < 1 := by
  simp_rw [@div_lt_one ℝ _ _ _ (Nat.cast_pos.mpr (Nat.factorial_pos _))]
  obtain ⟨p, hp, prime_p, h⟩ := linear_independent_exp_exists_prime_nat n ⌈|a|⌉.natAbs ⌈|c|⌉.natAbs
  use p, hp, prime_p
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
  rwa [Nat.cast_lt]
#align linear_independent_exp_exists_prime linear_independent_exp_exists_prime
