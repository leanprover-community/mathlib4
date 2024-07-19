/-
Copyright (c) 2024 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan, Thomas Browning
-/
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic

/-!

# Primality of `a ^ n + 1`

Euler proved around 1738 that some Fermat numbers are prime, but not `F₅`.
-/

open Nat

/-- `a ^ n + 1` is prime only if `n` is a power of two. -/
theorem pow_of_pow_add_prime (a n : ℕ) (ha : 1 < a) (hn : 1 < n) (hP : Nat.Prime (a ^ n + 1)) :
    ∃ m : ℕ, n = 2 ^ m := by
  obtain ⟨k, m, hm, rfl⟩ := exists_eq_two_pow_mul_odd (one_pos.trans hn).ne'
  rw [pow_mul] at hP
  use k
  replace ha : 1 < a ^ 2 ^ k := one_lt_pow (pow_ne_zero k two_ne_zero) ha
  have h := hm.nat_add_dvd_pow_add_pow (a ^ 2 ^ k) 1
  rw [one_pow, hP.dvd_iff_eq (Nat.lt_add_right 1 ha).ne', add_left_inj, pow_eq_self_iff ha] at h
  rw [h, mul_one]

theorem not_all_pow_pow_add_prime : ¬ ∀ n : ℕ, Nat.Prime (2 ^ (2 ^ n) + 1) := by
  intro h
  specialize h 5
  norm_num at h
  have : 4294967297 = 641 * 6700417 := by norm_num
  rw [this] at h
  have h' : ¬ Nat.Prime (641 * 6700417) := by
    apply Nat.not_prime_mul
    norm_num
    norm_num
  exact h' h
