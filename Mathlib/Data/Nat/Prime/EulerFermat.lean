/-
Copyright (c) 2024 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan, Thomas Browning
-/
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Primality of `a ^ n + 1`
-/

open Nat

/-- Prime `a ^ n + 1` implies `n` is a power of two. -/
theorem pow_of_pow_add_prime {a n : ℕ} (ha : 1 < a) (hn : 1 < n) (hP : (a ^ n + 1).Prime) :
    ∃ m : ℕ, n = 2 ^ m := by
  obtain ⟨k, m, hm, rfl⟩ := exists_eq_two_pow_mul_odd (one_pos.trans hn).ne'
  rw [pow_mul] at hP
  use k
  replace ha : 1 < a ^ 2 ^ k := one_lt_pow (pow_ne_zero k two_ne_zero) ha
  have h := hm.nat_add_dvd_pow_add_pow (a ^ 2 ^ k) 1
  rw [one_pow, hP.dvd_iff_eq (Nat.lt_add_right 1 ha).ne', add_left_inj, pow_eq_self_iff ha] at h
  rw [h, mul_one]

/-!
# Primality of `a ^ n - 1`
-/

/-- Prime `a ^ n - 1` implies either `a = 2` or prime `n`. -/
theorem prime_of_pow_sub_one_prime (a n : ℕ) (ha : 1 < a) (hn : 1 < n) (hP : (a ^ n - 1).Prime) :
    a = 2 ∧ n.Prime := by
  by_contra h₀
  have h₁ : a ≠ 2 ∨ ¬ n.Prime := by
    exact (Decidable.not_and_iff_or_not (a = 2) (Nat.Prime n)).mp h₀
  have h₂ (h : a ≠ 2) : ¬ (a ^ n - 1).Prime := by
    by_contra h₅
    have : (a - 1) ∣ a ^ n - 1 := by
      nth_rw 2 [← Nat.one_pow n]
      apply nat_sub_dvd_pow_sub_pow a 1 n
    have : ¬ (a ^ n - 1).Prime := by
      apply not_prime_of_dvd_of_ne this
      · omega
      · have : a ≠ a ^ n := Nat.ne_of_lt (lt_self_pow ha hn)
        omega
    contradiction
  have h₃ (hnP : ¬ n.Prime) : ¬ (a ^ n - 1).Prime := by
    have h₄ := hnP
    have minFac_lt : n.minFac < n := (not_prime_iff_minFac_lt hn).mp hnP
    have lt_minFac : 1 < n.minFac := by
      have : n.minFac = 0 ∨ n.minFac = 1 ∨ 1 < n.minFac := by omega
      rcases this with h | _ | h
      · by_contra; exact (not_eq_zero_of_lt (minFac_pos n)) h
      · have : ¬n = 1 := Nat.ne_of_lt' hn
        by_contra; simp_all only [minFac_eq_one_iff]
      · exact h
    apply (not_prime_iff_exists_dvd_ne (n := a ^ n - 1) (Prime.two_le hP)).mpr
    apply (not_prime_iff_exists_dvd_ne (n := n) hn).mp at h₄
    use a ^ minFac n - 1
    have h₅ : a < a ^ n.minFac := lt_self_pow ha lt_minFac
    have h₆ (x m n : ℕ) : x ^ m - 1 ∣ x ^ (m * n) - 1 := by
      nth_rw 2 [← Nat.one_pow n]
      rw [Nat.pow_mul x m n]
      apply nat_sub_dvd_pow_sub_pow (x ^ m) 1
    constructor
    · match exists_eq_mul_left_of_dvd (minFac_dvd n) with
      | ⟨m, hm⟩ =>
          nth_rw 2 [hm]
          rw [mul_comm]
          exact h₆ a n.minFac m
    · constructor
      · rw [ne_eq, pred_eq_succ_iff, zero_add]
        omega
      · rw [ne_eq]
        have : ¬ a ^ n.minFac = a ^ n := Nat.ne_of_lt <| pow_lt_pow_right ha minFac_lt
        have : 0 < a ^ n.minFac := zero_lt_of_lt h₅
        have : 0 < a ^ n := by exact zero_lt_of_lt <| lt_self_pow ha hn
        omega
  rcases h₁ with h₁' | h₁'
  · apply h₂ at h₁'
    contradiction
  · apply h₃ at h₁'
    contradiction
