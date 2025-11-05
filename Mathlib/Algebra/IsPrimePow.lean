/-
Copyright (c) 2022 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Order.Nat
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Pow

/-!
# Prime powers

This file deals with prime powers: numbers which are positive integer powers of a single prime.
-/
assert_not_exists Nat.divisors

variable {R : Type*} [CommMonoidWithZero R] (n p : R) (k : ℕ)

/-- `n` is a prime power if there is a prime `p` and a positive natural `k` such that `n` can be
written as `p^k`. -/
def IsPrimePow : Prop :=
  ∃ (p : R) (k : ℕ), Prime p ∧ 0 < k ∧ p ^ k = n

theorem isPrimePow_def : IsPrimePow n ↔ ∃ (p : R) (k : ℕ), Prime p ∧ 0 < k ∧ p ^ k = n :=
  Iff.rfl

/-- An equivalent definition for prime powers: `n` is a prime power iff there is a prime `p` and a
natural `k` such that `n` can be written as `p^(k+1)`. -/
theorem isPrimePow_iff_pow_succ : IsPrimePow n ↔ ∃ (p : R) (k : ℕ), Prime p ∧ p ^ (k + 1) = n :=
  (isPrimePow_def _).trans
    ⟨fun ⟨p, k, hp, hk, hn⟩ => ⟨p, k - 1, hp, by rwa [Nat.sub_add_cancel hk]⟩, fun ⟨_, _, hp, hn⟩ =>
      ⟨_, _, hp, Nat.succ_pos', hn⟩⟩

theorem not_isPrimePow_zero [NoZeroDivisors R] : ¬IsPrimePow (0 : R) := by
  simp only [isPrimePow_def, not_exists, not_and', and_imp]
  intro x n _hn hx
  rw [eq_zero_of_pow_eq_zero hx]
  simp

theorem IsPrimePow.not_unit {n : R} (h : IsPrimePow n) : ¬IsUnit n :=
  let ⟨_p, _k, hp, hk, hn⟩ := h
  hn ▸ (isUnit_pow_iff hk.ne').not.mpr hp.not_unit

theorem IsUnit.not_isPrimePow {n : R} (h : IsUnit n) : ¬IsPrimePow n := fun h' => h'.not_unit h

theorem not_isPrimePow_one : ¬IsPrimePow (1 : R) :=
  isUnit_one.not_isPrimePow

theorem Prime.isPrimePow {p : R} (hp : Prime p) : IsPrimePow p :=
  ⟨p, 1, hp, zero_lt_one, by simp⟩

theorem IsPrimePow.pow {n : R} (hn : IsPrimePow n) {k : ℕ} (hk : k ≠ 0) : IsPrimePow (n ^ k) :=
  let ⟨p, k', hp, hk', hn⟩ := hn
  ⟨p, k * k', hp, mul_pos hk.bot_lt hk', by rw [pow_mul', hn]⟩

theorem IsPrimePow.ne_zero [NoZeroDivisors R] {n : R} (h : IsPrimePow n) : n ≠ 0 := fun t =>
  not_isPrimePow_zero (t ▸ h)

theorem IsPrimePow.ne_one {n : R} (h : IsPrimePow n) : n ≠ 1 := fun t =>
  not_isPrimePow_one (t ▸ h)

section Nat

theorem isPrimePow_nat_iff (n : ℕ) : IsPrimePow n ↔ ∃ p k : ℕ, Nat.Prime p ∧ 0 < k ∧ p ^ k = n := by
  simp only [isPrimePow_def, Nat.prime_iff]

theorem Nat.Prime.isPrimePow {p : ℕ} (hp : p.Prime) : IsPrimePow p :=
  _root_.Prime.isPrimePow (prime_iff.mp hp)

set_option linter.style.commandStart false in -- TODO decide about this!
theorem isPrimePow_nat_iff_bounded (n : ℕ) :
    IsPrimePow n ↔ ∃ p : ℕ, p ≤ n ∧ ∃ k : ℕ, k ≤ n ∧ p.Prime ∧ 0 < k ∧ p ^ k = n := by
  rw [isPrimePow_nat_iff]
  refine Iff.symm ⟨fun ⟨p, _, k, _, hp, hk, hn⟩ => ⟨p, k, hp, hk, hn⟩, ?_⟩
  rintro ⟨p, k, hp, hk, rfl⟩
  refine ⟨p, ?_, k, (Nat.lt_pow_self hp.one_lt).le, hp, hk, rfl⟩
  conv => { lhs; rw [← (pow_one p)] }
  exact Nat.pow_le_pow_right hp.one_lt.le hk

theorem isPrimePow_nat_iff_bounded_log (n : ℕ) :
    IsPrimePow n
      ↔ ∃ k : ℕ, k ≤ Nat.log 2 n ∧ 0 < k ∧ ∃ p : ℕ, p ≤ n ∧ n = p ^ k ∧ p.Prime := by
  rw [isPrimePow_nat_iff]
  constructor
  · rintro ⟨p, k, hp', hk', rfl⟩
    refine ⟨k, ?_, hk', ⟨p, Nat.le_pow hk', rfl, hp'⟩⟩
    · calc
        k = Nat.log 2 (2 ^ k) := by simp
        _ ≤ Nat.log 2 (p ^ k) := Nat.log_mono Nat.one_lt_two Nat.AtLeastTwo.prop
                                   (Nat.pow_le_pow_left (Nat.Prime.two_le hp') k)
  · rintro ⟨k, hk, hk', ⟨p, hp, rfl, hp'⟩⟩
    exact ⟨p, k, hp', hk', rfl⟩

theorem isPrimePow_nat_iff_bounded_log_minFac (n : ℕ) :
    IsPrimePow n
      ↔ ∃ k : ℕ, k ≤ Nat.log 2 n ∧ 0 < k ∧ n = n.minFac ^ k := by
  rw [isPrimePow_nat_iff_bounded_log]
  obtain rfl | h := eq_or_ne n 1
  · simp
  constructor
  · rintro ⟨k, hkle, hk_pos, p, hle, heq, hprime⟩
    refine ⟨k, hkle, hk_pos, ?_⟩
    rw [heq, hprime.pow_minFac hk_pos.ne']
  · rintro ⟨k, hkle, hk_pos, heq⟩
    refine ⟨k, hkle, hk_pos, n.minFac, Nat.minFac_le ?_, heq, ?_⟩
    · grind [Nat.minFac_prime_iff, nonpos_iff_eq_zero, Nat.log_zero_right, lt_self_iff_false]
    · grind [Nat.minFac_prime_iff]

instance {n : ℕ} : Decidable (IsPrimePow n) :=
  decidable_of_iff' _ (isPrimePow_nat_iff_bounded_log_minFac n)

theorem IsPrimePow.dvd {n m : ℕ} (hn : IsPrimePow n) (hm : m ∣ n) (hm₁ : m ≠ 1) : IsPrimePow m := by
  grind [isPrimePow_nat_iff, Nat.dvd_prime_pow, Nat.pow_eq_one]

theorem IsPrimePow.two_le : ∀ {n : ℕ}, IsPrimePow n → 2 ≤ n
  | 0, h => (not_isPrimePow_zero h).elim
  | 1, h => (not_isPrimePow_one h).elim
  | _n + 2, _ => le_add_self

theorem IsPrimePow.pos {n : ℕ} (hn : IsPrimePow n) : 0 < n :=
  pos_of_gt hn.two_le

theorem IsPrimePow.one_lt {n : ℕ} (h : IsPrimePow n) : 1 < n :=
  h.two_le

end Nat
