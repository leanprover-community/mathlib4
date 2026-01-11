/-
Copyright (c) 2025 Zhipeng Chen, Haolun Tang, Jing Yi Zhan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhipeng Chen, Haolun Tang, Jing Yi Zhan
-/
import Mathlib.NumberTheory.UnitaryDivisor
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Factorization.Induction

/-!
# Unitary Perfect Numbers

This file defines unitary perfect numbers and proves that no odd unitary perfect numbers exist.

A positive integer `n` is *unitary perfect* if `σ*(n) = 2n`, where `σ*` is the unitary divisor
sum function. This is analogous to the classical definition of perfect numbers using `σ(n) = 2n`.

The main result is that all unitary perfect numbers are even, proved by showing that `σ*(n)` for
odd `n > 1` is always even, and for odd composite `n`, `σ*(n)` is divisible by 4, while `2n` is
divisible by exactly 2.

## Main Definitions

* `Nat.UnitaryPerfect n`: Predicate stating that `n` is a unitary perfect number.

## Main Results

* `Nat.no_odd_unitary_perfect`: There are no odd unitary perfect numbers greater than 1.
* `Nat.UnitaryPerfect.even`: Every unitary perfect number is even.
* `Nat.UnitaryPerfect.eq_two_pow_mul_odd`: Every unitary perfect number has the form `2^a * k`
  where `a ≥ 1` and `k` is odd.

## References

* Subbarao, M. V., & Warren, L. J. (1966). Unitary perfect numbers.
  Canadian Mathematical Bulletin, 9(2), 147-153.
* Wall, C. R. (1975). The fifth unitary perfect number.
  Canadian Mathematical Bulletin, 18(1), 115-122.

## Tags

unitary perfect number, perfect number, number theory
-/

namespace Nat

open BigOperators

/-! ### Definition -/

/-- A positive integer `n` is *unitary perfect* if `σ*(n) = 2n`. -/
def UnitaryPerfect (n : ℕ) : Prop :=
  n ≠ 0 ∧ σ* n = 2 * n

/-! ### Parity Lemmas -/

/-- `σ*(p^k)` is even when `p` is odd and `k ≥ 1`. -/
theorem unitaryDivisorSum_odd_prime_pow_even {p k : ℕ} (hp : Nat.Prime p) (hodd : Odd p)
    (hk : 0 < k) : Even (σ* (p ^ k)) := by
  have hk_ne : k ≠ 0 := Nat.pos_iff_ne_zero.mp hk
  rw [unitaryDivisorSum_prime_pow hp hk_ne]
  have hp_odd_pow : Odd (p ^ k) := Odd.pow hodd
  rw [Nat.even_add_one]
  exact Nat.not_even_iff_odd.symm.mp hp_odd_pow

/-- For any odd `n > 1`, `σ*(n)` is even. -/
theorem unitaryDivisorSum_odd_even {n : ℕ} (hn : 1 < n) (hodd : Odd n) : Even (σ* n) := by
  induction n using Nat.recOnPrimeCoprime with
  | h0 => omega
  | hp p k hp_prime =>
    have hp_odd : Odd p := by
      rcases hp_prime.eq_two_or_odd with hp_2 | hp_mod
      · subst hp_2
        have hk_ne : k ≠ 0 := by intro hk0; subst hk0; simp only [pow_zero] at hn
        have heven : Even ((2 : ℕ) ^ k) := Even.pow_of_ne_zero even_two hk_ne
        exact absurd heven (Nat.not_even_iff_odd.symm.mp hodd)
      · exact Nat.odd_iff.mpr hp_mod
    have hk_pos : 0 < k := by
      by_contra hk0; simp only [not_lt, nonpos_iff_eq_zero] at hk0; subst hk0
      simp only [pow_zero] at hn
    exact unitaryDivisorSum_odd_prime_pow_even hp_prime hp_odd hk_pos
  | h a b ha hb hcoprime iha ihb =>
    have ha_pos : a ≠ 0 := by omega
    have hb_pos : b ≠ 0 := by omega
    rw [unitaryDivisorSum_mul hcoprime ha_pos hb_pos]
    have ⟨ha_odd, hb_odd⟩ := Nat.odd_mul.mp hodd
    exact Even.mul_right (iha ha ha_odd) (σ* b)

/-- For odd `n = a*b` with coprime `a, b > 1`, we have `4 ∣ σ*(n)`. -/
theorem unitaryDivisorSum_coprime_four_dvd {a b : ℕ} (ha : 1 < a) (hb : 1 < b)
    (hcoprime : Nat.Coprime a b) (ha_odd : Odd a) (hb_odd : Odd b) : 4 ∣ σ* (a * b) := by
  have ha_pos : a ≠ 0 := by omega
  have hb_pos : b ≠ 0 := by omega
  rw [unitaryDivisorSum_mul hcoprime ha_pos hb_pos]
  have hsa_even : Even (σ* a) := unitaryDivisorSum_odd_even ha ha_odd
  have hsb_even : Even (σ* b) := unitaryDivisorSum_odd_even hb hb_odd
  obtain ⟨x, hx⟩ := hsa_even
  obtain ⟨y, hy⟩ := hsb_even
  use x * y
  calc σ* a * σ* b = (x + x) * (y + y) := by rw [hx, hy]
    _ = 4 * (x * y) := by ring

/-- `4` does not divide `2*n` when `n` is odd. -/
theorem four_not_dvd_two_mul_odd {n : ℕ} (hodd : Odd n) : ¬(4 ∣ 2 * n) := by
  intro h4dvd
  obtain ⟨k, hk⟩ := h4dvd
  have heven : Even n := ⟨k, by omega⟩
  exact Nat.not_even_iff_odd.symm.mp hodd heven

/-! ### Main Theorem -/

/-- **No odd unitary perfect numbers exist**.

This is the main theorem of the file. The proof proceeds by induction on the prime
factorization structure using `Nat.recOnPrimeCoprime`:

1. **Prime power case** (`n = p^k`): If `p` is odd, then `σ*(p^k) = p^k + 1`. The equation
   `p^k + 1 = 2p^k` implies `p^k = 1`, which is impossible for `p ≥ 3`.

2. **Coprime product case** (`n = a*b`): Both `a` and `b` must be odd (since `n` is odd).
   By the parity lemma, both `σ*(a)` and `σ*(b)` are even, so `σ*(n) = σ*(a)σ*(b)` is
   divisible by 4. But `2n` is divisible by exactly 2 (since `n` is odd), contradiction. -/
theorem no_odd_unitary_perfect {n : ℕ} (hodd : Odd n) (hgt1 : n > 1) : ¬UnitaryPerfect n := by
  intro ⟨hn0, hup⟩
  induction n using Nat.recOnPrimeCoprime with
  | h0 => omega
  | hp p k hp_prime =>
    have hp_odd : Odd p := by
      rcases hp_prime.eq_two_or_odd with hp_2 | hp_mod
      · subst hp_2
        have hk_ne : k ≠ 0 := by intro hk0; subst hk0; simp only [pow_zero] at hgt1
        have heven : Even ((2 : ℕ) ^ k) := Even.pow_of_ne_zero even_two hk_ne
        exact absurd heven (Nat.not_even_iff_odd.symm.mp hodd)
      · exact Nat.odd_iff.mpr hp_mod
    have hk_pos : 0 < k := by by_contra hk0; simp only [not_lt, nonpos_iff_eq_zero] at hk0
      subst hk0; simp only [pow_zero] at hgt1
    have hk_ne : k ≠ 0 := Nat.pos_iff_ne_zero.mp hk_pos
    rw [unitaryDivisorSum_prime_pow hp_prime hk_ne] at hup
    have hp_ge_3 : p ≥ 3 := by
      have := hp_prime.two_le
      have hp_ne_2 : p ≠ 2 := fun h => by
        subst h; exact Nat.not_even_iff_odd.symm.mp hp_odd even_two
      omega
    have hpk_ge : p ^ k ≥ p := by
      calc p ^ k ≥ p ^ 1 := Nat.pow_le_pow_right hp_prime.pos hk_pos
        _ = p := pow_one p
    have : p ^ k ≥ 3 := by omega
    omega
  | h a b ha hb hcoprime _ _ =>
    have ⟨ha_odd, hb_odd⟩ := Nat.odd_mul.mp hodd
    have h4dvd : 4 ∣ σ* (a * b) := unitaryDivisorSum_coprime_four_dvd ha hb hcoprime ha_odd hb_odd
    have h4_dvd_2n : 4 ∣ 2 * (a * b) := by rw [← hup]; exact h4dvd
    exact four_not_dvd_two_mul_odd hodd h4_dvd_2n

/-- Every unitary perfect number is even. -/
theorem UnitaryPerfect.even {n : ℕ} (h : UnitaryPerfect n) : Even n := by
  rcases Nat.even_or_odd n with heven | hodd
  · exact heven
  · obtain ⟨hn0, hsum⟩ := h
    by_cases hn_eq_1 : n = 1
    · rw [hn_eq_1, unitaryDivisorSum_one] at hsum
      omega
    · have hgt1 : n > 1 := by
        rcases n with _ | n'
        · exact absurd rfl hn0
        · rcases n' with _ | _
          · exact absurd rfl hn_eq_1
          · omega
      exact absurd ⟨hn0, hsum⟩ (no_odd_unitary_perfect hodd hgt1)

/-- Every unitary perfect number can be written as `2^a * k` where `a ≥ 1` and `k` is odd. -/
theorem UnitaryPerfect.eq_two_pow_mul_odd {n : ℕ} (h : UnitaryPerfect n) :
    ∃ a k : ℕ, a ≥ 1 ∧ Odd k ∧ n = 2 ^ a * k := by
  have heven := h.even
  obtain ⟨hn0, _⟩ := h
  obtain ⟨a, k, hk_odd, hdecomp⟩ := Nat.exists_eq_two_pow_mul_odd hn0
  refine ⟨a, k, ?_, hk_odd, hdecomp⟩
  by_contra ha_zero
  push_neg at ha_zero
  interval_cases a
  rw [hdecomp, pow_zero, one_mul] at heven
  exact absurd hk_odd (Nat.not_odd_iff_even.mpr heven)

end Nat
