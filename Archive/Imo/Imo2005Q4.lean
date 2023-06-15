/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth

! This file was ported from Lean 3 source module imo.imo2005_q4
! leanprover-community/mathlib commit 308826471968962c6b59c7ff82a22757386603e3
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.FieldTheory.Finite.Basic

/-!
# IMO 2005 Q4

Problem: Determine all positive integers relatively prime to all the terms of the infinite sequence
`a n = 2 ^ n + 3 ^ n + 6 ^ n - 1`, for `n ≥ 1`.

This is quite an easy problem, in which the key point is a modular arithmetic calculation with
the sequence `a n` relative to an arbitrary prime.
-/


namespace IMO2005Q4

/-- The sequence considered in the problem, `2 ^ n + 3 ^ n + 6 ^ n - 1`. -/
def a (n : ℕ) : ℤ :=
  2 ^ n + 3 ^ n + 6 ^ n - 1
#align imo2005_q4.a IMO2005Q4.a

/-- Key lemma (a modular arithmetic calculation):  Given a prime `p` other than `2` or `3`, the
`p - 2`th term of the sequence has `p` as a factor. -/
theorem find_specified_factor {p : ℕ} (hp : Nat.Prime p) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    ↑p ∣ a (p - 2) := by
  -- restate in terms of `ZMod p`
  have := Fact.mk hp
  rw [← ZMod.int_cast_zmod_eq_zero_iff_dvd, a]
  push_cast
  have hle : 1 ≤ p - 1 := le_tsub_of_add_le_right hp.two_le
  -- reformulate assumptions `p ≠ 2` and `p ≠ 3` in `ZMod p`
  replace hp2 : (2 : ZMod p) ≠ 0
  · rwa [← Nat.cast_ofNat, Ne.def, ZMod.nat_cast_zmod_eq_zero_iff_dvd,
      Nat.prime_dvd_prime_iff_eq hp Nat.prime_two]
  replace hp3 : (3 : ZMod p) ≠ 0
  · rwa [← Nat.cast_ofNat, Ne.def, ZMod.nat_cast_zmod_eq_zero_iff_dvd,
      Nat.prime_dvd_prime_iff_eq hp Nat.prime_three]
  -- main computation
  calc
    (2 : ZMod p) ^ (p - 2) + 3 ^ (p - 2) + 6 ^ (p - 2) - 1
      = 2 ^ (p - 1 - 1) + 3 ^ (p - 1 - 1) + (2 * 3) ^ (p - 1 - 1) - 1 := by congr 3; norm_num
    _ = 1 / 2 + 1 / 3 + (1 / 2) * (1 / 3) - 1 := by
      simp [pow_sub₀, mul_pow, ZMod.pow_card_sub_one_eq_one, mul_comm, *]
    _ = 0 := by field_simp; norm_num
#align imo2005_q4.find_specified_factor IMO2005Q4.find_specified_factor

end IMO2005Q4

open IMO2005Q4

/-- Main statement:  The only positive integer coprime to all terms of the sequence `a` is `1`. -/
theorem imo2005_q4 {k : ℕ} (hk : 0 < k) : (∀ n : ℕ, 1 ≤ n → IsCoprime (a n) k) ↔ k = 1 := by
  constructor; rotate_left
  · -- The property is clearly true for `k = 1`
    rintro rfl n -
    exact isCoprime_one_right
  intro h
  -- Conversely, suppose `k` is a number with the property, and let `p` be `k.min_fac` (by
  -- definition this is the minimal prime factor of `k` if `k ≠ 1`, and otherwise `1`.
  let p := k.minFac
  -- Suppose for the sake of contradiction that `k ≠ 1`.  Then `p` is genuinely a prime factor of
  -- `k`. Hence, it divides none of `a n`, `1 ≤ n`
  by_contra hk'
  have hp : Nat.Prime p := Nat.minFac_prime hk'
  replace h : ∀ n, 1 ≤ n → ¬(p : ℤ) ∣ a n := fun n hn ↦ by
    have : IsCoprime (a n) p :=
      .of_isCoprime_of_dvd_right (h n hn) (Int.coe_nat_dvd.mpr k.minFac_dvd)
    rwa [isCoprime_comm,(Nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd] at this
  -- For `p = 2` and `p = 3`, take `n = 1` and `n = 2`, respectively
  by_cases hp2 : p = 2
  · rw [hp2] at h
    apply h 1 <;> norm_num
  by_cases hp3 : p = 3
  · rw [hp3] at h
    apply h 2 <;> norm_num
  -- Otherwise, take `n = p - 2`
  refine h (p - 2) ?_ (find_specified_factor hp hp2 hp3)
  calc
    1 = 3 - 2 := by norm_num
    _ ≤ p - 2 := tsub_le_tsub_right (Nat.succ_le_of_lt $ hp.two_le.lt_of_ne' hp2) _
#align imo2005_q4 imo2005_q4

