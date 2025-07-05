/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
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

/-- Key lemma (a modular arithmetic calculation):  Given a prime `p` other than `2` or `3`, the
`(p - 2)`th term of the sequence has `p` as a factor. -/
theorem find_specified_factor {p : ℕ} (hp : Nat.Prime p) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    ↑p ∣ a (p - 2) := by
  -- Since `p` is neither `2` nor `3`, it is coprime with `2`, `3`, and `6`
  rw [Ne, ← Nat.prime_dvd_prime_iff_eq hp (by decide), ← Nat.Prime.coprime_iff_not_dvd hp]
    at hp2 hp3
  have : Int.gcd p 6 = 1 := Nat.coprime_mul_iff_right.2 ⟨hp2, hp3⟩
  -- Nat arithmetic needed to deal with powers
  have hp' : p - 1 = p - 2 + 1 := Eq.symm <| Nat.succ_pred <| (tsub_pos_of_lt hp.one_lt).ne'
  -- Thus it suffices to show that `6 * a (p - 2) ≡ 0 [ZMOD p]`
  rw [← Int.modEq_zero_iff_dvd, ← Int.ediv_one p, ← Nat.cast_one, ← this]
  refine Int.ModEq.cancel_left_div_gcd (Nat.cast_pos.2 hp.pos) ?_
  calc
    6 * a (p - 2) = 3 * 2 ^ (p - 1) + 2 * 3 ^ (p - 1) + (2 * 3) ^ (p - 1) - 6 := by
      simp only [a, hp', pow_succ']; ring
    _ ≡ 3 * 1 + 2 * 1 + 1 - 6 [ZMOD p] := by
      gcongr <;> apply Int.ModEq.pow_card_sub_one_eq_one hp <;>
        rwa [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]
    _ = 0 := rfl

end IMO2005Q4

open IMO2005Q4

/-- Main statement:  The only positive integer coprime to all terms of the sequence `a` is `1`. -/
theorem imo2005_q4 {k : ℕ} (hk : 0 < k) : (∀ n : ℕ, 1 ≤ n → IsCoprime (a n) k) ↔ k = 1 := by
  constructor; rotate_left
  · -- The property is clearly true for `k = 1`
    rintro rfl n -
    exact isCoprime_one_right
  intro h
  -- Conversely, suppose `k` is a number with the property, and let `p` be `k.minFac` (by
  -- definition this is the minimal prime factor of `k` if `k ≠ 1`, and otherwise `1`.
  let p := k.minFac
  -- Suppose for the sake of contradiction that `k ≠ 1`.  Then `p` is genuinely a prime factor of
  -- `k`. Hence, it divides none of `a n`, `1 ≤ n`
  by_contra hk'
  have hp : Nat.Prime p := Nat.minFac_prime hk'
  replace h : ∀ n, 1 ≤ n → ¬(p : ℤ) ∣ a n := fun n hn ↦ by
    have : IsCoprime (a n) p :=
      .of_isCoprime_of_dvd_right (h n hn) (Int.natCast_dvd_natCast.mpr k.minFac_dvd)
    rwa [isCoprime_comm,(Nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd] at this
  -- For `p = 2` and `p = 3`, take `n = 1` and `n = 2`, respectively
  by_cases hp2 : p = 2
  · rw [hp2] at h
    apply h 1 <;> decide
  by_cases hp3 : p = 3
  · rw [hp3] at h
    apply h 2 <;> decide
  -- Otherwise, take `n = p - 2`
  refine h (p - 2) ?_ (find_specified_factor hp hp2 hp3)
  calc
    1 = 3 - 2 := by simp
    _ ≤ p - 2 := tsub_le_tsub_right (Nat.succ_le_of_lt <| hp.two_le.lt_of_ne' hp2) _
