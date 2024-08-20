/-
Copyright (c) 2024 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan, Thomas Browning
-/
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.LucasPrimality

/-!
# Lemmas about Fermat numbers
-/

open ZMod Nat

/-- Prime `a ^ n + 1` implies `n` is a power of two (Fermat primes). -/
theorem pow_of_pow_add_prime {a n : ℕ} (ha : 1 < a) (hn : n ≠ 0) (hP : (a ^ n + 1).Prime) :
    ∃ m : ℕ, n = 2 ^ m := by
  obtain ⟨k, m, hm, rfl⟩ := exists_eq_two_pow_mul_odd hn
  rw [pow_mul] at hP
  use k
  replace ha : 1 < a ^ 2 ^ k := one_lt_pow (pow_ne_zero k two_ne_zero) ha
  let h := hm.nat_add_dvd_pow_add_pow (a ^ 2 ^ k) 1
  rw [one_pow, hP.dvd_iff_eq (Nat.lt_add_right 1 ha).ne', add_left_inj, pow_eq_self_iff ha] at h
  rw [h, mul_one]

/-- `Fₙ = 2^(2^n)+1` is prime only if `3^(2^(2^n-1)) = -1 mod Fₙ` (Pépin's test). -/
lemma pepin_primality (n : ℕ) (h : 3 ^ (2 ^ (2 ^ n - 1)) = (-1 : ZMod (2 ^ (2 ^ n) + 1))) :
    (2 ^ (2 ^ n) + 1).Prime := by
  have := Fact.mk (succ_lt_succ (Nat.one_lt_pow (pow_ne_zero n two_ne_zero) one_lt_two))
  have key : 2 ^ n = 2 ^ n - 1 + 1 := (Nat.sub_add_cancel Nat.one_le_two_pow).symm
  apply lucas_primality (p := 2 ^ (2 ^ n) + 1) (a := 3)
  · rw [Nat.add_sub_cancel, key, pow_succ, pow_mul, ← pow_succ, ← key, h, neg_one_sq]
  · intro p hp1 hp2
    rw [Nat.add_sub_cancel, (Nat.prime_dvd_prime_iff_eq hp1 prime_two).mp (hp1.dvd_of_dvd_pow hp2),
        key, pow_succ, Nat.mul_div_cancel _ two_pos, ← pow_succ, ← key, h]
    exact ZMod.neg_one_ne_one

/-- Prime factors of `a ^ (2 ^ n) + 1`, `1 < n`, are of form `k * 2 ^ (n + 1) + 1`. -/
lemma pow_pow_add_primeFactors_one_lt {a n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpdvd : p ∣ a ^ (2 ^ n) + 1) :
    ∃ k, p = k * 2 ^ (n + 1) + 1 := by
  have : Fact (2 < p) := Fact.mk (lt_of_le_of_ne hp.two_le hp2.symm)
  have : Fact p.Prime := Fact.mk hp
  have ha1 : (a : ZMod p) ^ (2 ^ n) = -1 := by
    rw [eq_neg_iff_add_eq_zero]
    exact_mod_cast (natCast_zmod_eq_zero_iff_dvd (a ^ (2 ^ n) + 1) p).mpr hpdvd
  have ha0 : (a : ZMod p) ≠ 0 := by
    intro h
    rw [h, zero_pow (pow_ne_zero n two_ne_zero), zero_eq_neg] at ha1
    exact one_ne_zero ha1
  have ha : orderOf (a : ZMod p) = 2 ^ (n + 1) := by
    apply orderOf_eq_prime_pow
    · rw [ha1]
      exact ZMod.neg_one_ne_one
    · rw [pow_succ, pow_mul, ha1, neg_one_sq]
  simpa [ha, dvd_def, Nat.sub_eq_iff_eq_add hp.one_le, mul_comm] using orderOf_dvd_card_sub_one ha0

/-- Prime factors of `Fₙ = 2 ^ (2 ^ n) + 1`, `1 < n`, are of form `k * 2 ^ (n + 2) + 1`. -/
lemma fermat_primeFactors_one_lt (n p : ℕ) (hn : 1 < n) (hp : p.Prime)
    (hpdvd : p ∣ 2 ^ (2 ^ n) + 1) :
    ∃ k, p = k * 2 ^ (n + 2) + 1 := by
  have : Fact p.Prime := Fact.mk hp
  have hp2 : p ≠ 2 := by
    exact ((even_pow.mpr ⟨even_two, pow_ne_zero n two_ne_zero⟩).add_one).ne_two_of_dvd_nat hpdvd
  have hp8 : p % 8 = 1 := by
    obtain ⟨k, rfl⟩ := pow_pow_add_primeFactors_one_lt hp hp2 hpdvd
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hn
    rw [add_assoc, pow_add, ← mul_assoc, ← mod_add_mod, mul_mod]
    norm_num
  obtain ⟨a, ha⟩ := (exists_sq_eq_two_iff hp2).mpr (Or.inl hp8)
  suffices h : p ∣ a.val ^ (2 ^ (n + 1)) + 1 by
    exact pow_pow_add_primeFactors_one_lt hp hp2 h
  rw [← natCast_zmod_eq_zero_iff_dvd, Nat.cast_add, Nat.cast_one, Nat.cast_pow] at hpdvd ⊢
  rwa [ZMod.natCast_val, ZMod.cast_id, pow_succ', pow_mul, sq, ← ha]

/-- Prime factors of `Fₙ = 2 ^ (2 ^ n) + 1` are either 3, 5, or of form `k * 2 ^ (n + 2) + 1`. -/
lemma fermat_primeFactors (n p : ℕ) (hP : p.Prime)
    (hpdvd : p ∣ 2 ^ (2 ^ n) + 1) :
    p = 3 ∨ p = 5 ∨ ∃ k, p = k * 2 ^ (n + 2) + 1 := by
  obtain h | ⟨h | h⟩ : n = 0 ∨ n = 1 ∨ 1 < n := by omega
  · left
    rw [h] at hpdvd
    exact (prime_dvd_prime_iff_eq hP prime_three).mp hpdvd
  · right; left
    rw [h] at hpdvd
    norm_num at hpdvd
    exact (prime_dvd_prime_iff_eq hP prime_five).mp hpdvd
  · right; right
    exact fermat_primeFactors_one_lt n p h hP hpdvd

/-!
# Primality of Mersenne numbers `Mₙ = a ^ n - 1`
-/

/-- Prime `a ^ n - 1` implies `a = 2` and prime `n`. -/
theorem prime_of_pow_sub_one_prime {a n : ℕ} (hn1 : n ≠ 1) (hP : (a ^ n - 1).Prime) :
    a = 2 ∧ n.Prime := by
  have han1 : 1 < a ^ n := tsub_pos_iff_lt.mp hP.pos
  have hn0 : n ≠ 0 := fun h ↦ (h ▸ han1).ne' rfl
  have ha1 : 1 < a := (Nat.one_lt_pow_iff hn0).mp han1
  have ha0 : 0 < a := one_pos.trans ha1
  have ha2 : a = 2 := by
    contrapose! hn1
    let h := nat_sub_dvd_pow_sub_pow a 1 n
    rw [one_pow, hP.dvd_iff_eq (mt (Nat.sub_eq_iff_eq_add ha1.le).mp hn1), eq_comm] at h
    exact (pow_eq_self_iff ha1).mp (Nat.sub_one_cancel ha0 (pow_pos ha0 n) h).symm
  subst ha2
  refine ⟨rfl, Nat.prime_def_lt''.mpr ⟨(two_le_iff n).mpr ⟨hn0, hn1⟩, fun d hdn ↦ ?_⟩⟩
  have hinj : ∀ x y, 2 ^ x - 1 = 2 ^ y - 1 → x = y :=
    fun x y h ↦ Nat.pow_right_injective le_rfl (sub_one_cancel (pow_pos ha0 x) (pow_pos ha0 y) h)
  let h := nat_sub_dvd_pow_sub_pow (2 ^ d) 1 (n / d)
  rw [one_pow, ← pow_mul, Nat.mul_div_cancel' hdn] at h
  exact (hP.eq_one_or_self_of_dvd (2 ^ d - 1) h).imp (hinj d 1) (hinj d n)
