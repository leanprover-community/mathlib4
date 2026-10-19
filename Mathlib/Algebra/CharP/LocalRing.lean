/-
Copyright (c) 2022 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Eugster
-/
module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.IsPrimePow
public import Mathlib.RingTheory.LocalRing.Defs

import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Characteristics of local rings

## Main result

- `charP_zero_or_prime_power`: In a commutative local ring the characteristic is either
  zero or a prime power.

-/

public section

/-- In a local ring the characteristic is either zero or a prime power. -/
theorem charP_zero_or_prime_power (R : Type*) [Ring R] [IsLocalRing R] (q : ℕ)
    [char_R_q : CharP R q] : q = 0 ∨ IsPrimePow q := by
  -- Assume `q := char(R)` is not zero.
  refine or_iff_not_imp_left.mpr fun q_ne_zero => ?_
  -- Let `p` be the a prime factor of `q`, and write `q = p^n k` with `p ∤ k`.
  obtain ⟨p, p_prime, p_dvd_q⟩ : ∃ p, Nat.Prime p ∧ p ∣ q :=
    Nat.exists_prime_and_dvd (CharP.char_ne_one R q)
  obtain ⟨n, k, p_not_dvd_k, rfl⟩ : ∃ n k, ¬p ∣ k ∧ q = p ^ n * k :=
    Nat.exists_eq_pow_mul_and_not_dvd q_ne_zero p p_prime.ne_one
  have n_ne_zero : n ≠ 0 := fun hn => p_not_dvd_k (by simpa [hn] using p_dvd_q)
  clear q_ne_zero p_dvd_q
  -- Then `p^n` and `k` are coprime; say `p^n m + kt = 1` for some `m, t : ℤ`.
  obtain ⟨m, t, h⟩ : ∃ m t : ℤ, (p ^ n : ℕ) * m + k * t = 1 :=
    ⟨_, _, (Nat.gcd_eq_gcd_ab _ _).symm.trans <| congrArg Nat.cast <|
      (p_prime.coprime_iff_not_dvd.mpr p_not_dvd_k).pow_left n⟩
  -- Thus one of `p^n m` and `kt` is a unit in `R`.
  obtain h0 | h0 : IsUnit (((p ^ n : ℕ) * m : ℤ) : R) ∨ IsUnit ((k * t : ℤ) : R) :=
    IsLocalRing.isUnit_or_isUnit_of_add_one (by rw [← Int.cast_add, h, Int.cast_one])
  -- If `p^n` is a unit, then `p^n = 1`... contradiction.
  · replace h0 : (k : R) = 0 := by
      rw [← Int.cast_natCast, ← h0.mul_right_eq_zero, ← Int.cast_mul, mul_right_comm,
        ← Nat.cast_mul, Int.cast_mul, Int.cast_natCast, CharP.cast_eq_zero, zero_mul]
    replace h : k ≠ 0 := fun hk => p_not_dvd_k (hk ▸ p.dvd_zero)
    rw [← k.one_mul, CharP.cast_eq_zero_iff, mul_dvd_mul_iff_right h, Nat.dvd_one] at h0
    exact absurd h0 (Nat.one_lt_pow n_ne_zero p_prime.one_lt).ne.symm
  -- If `k` is a unit, then `k = 1`, so `p^n k = p^n` is a prime power.
  · replace h0 : ((p ^ n : ℕ) : R) = 0 := by
      rw [← Int.cast_natCast, ← h0.mul_left_eq_zero, ← Int.cast_mul, ← mul_assoc,
        ← Nat.cast_mul, Int.cast_mul, Int.cast_natCast, CharP.cast_eq_zero, zero_mul]
    replace h : p ^ n ≠ 0 := pow_ne_zero n p_prime.ne_zero
    rw [← (p ^ n).mul_one, CharP.cast_eq_zero_iff, mul_dvd_mul_iff_left h, Nat.dvd_one] at h0
    rw [h0, Nat.mul_one]
    exact p_prime.isPrimePow.pow n_ne_zero
