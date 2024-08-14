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
  have hneg1ne1: (-1 : ZMod (2 ^ (2 ^ n) + 1)) ≠ (1 : ZMod (2 ^ (2 ^ n) + 1)) := by
    by_contra h'
    let h := (ZMod.neg_eq_self_iff (1 : ZMod (2 ^ (2 ^ n) + 1))).mp h'
    rcases h with h | h
    · absurd h
      rw [Fin.one_eq_zero_iff, ← ne_eq, succ_ne_succ]
      exact NeZero.ne (2 ^ 2 ^ n)
    · absurd h
      have : Fact (1 < 2 ^ (2 ^ n) + 1) := by
        simp only [lt_add_iff_pos_left, ofNat_pos, pow_pos]
        exact { out := trivial }
      rw [val_one]
      norm_num
      simp only [reduceEqDiff]
      rw [pow_eq_one_iff (x := 2) (n := 2 ^ n)]
      · exact succ_succ_ne_one 0
      · exact Ne.symm (NeZero.ne' (2 ^ n))
  apply lucas_primality (p := 2 ^ (2 ^ n) + 1) (a := 3)
  · norm_num
    apply Mathlib.Tactic.Ring.pow_nat _ h neg_one_sq
    rw [mul_comm, ← Nat.pow_add' 2 (2 ^ n - 1) 1]
    norm_num
    rw [Nat.sub_add_cancel Nat.one_le_two_pow]
  · norm_num
    intro p H' H''
    rw [(Nat.prime_dvd_prime_iff_eq H' prime_two).mp ((Nat.Prime.dvd_of_dvd_pow H') H'')]
    have : 2 ^ (2 ^ n) / 2 = 2 ^ (2 ^ n - 1) := by
      rw [← Nat.mul_right_inj (a := 2), ← Nat.pow_add' 2 (2 ^ n - 1) 1,
        mul_comm, Nat.div_mul_cancel]
      · norm_num
        rw [Nat.sub_add_cancel Nat.one_le_two_pow]
      · exact dvd_pow_self 2 (Ne.symm (NeZero.ne' (2 ^ n)))
      · exact Ne.symm (zero_ne_add_one 1)
    rw [this, h]
    exact hneg1ne1

private lemma fermat_primeFactors_one_lt (n p : ℕ) (hn : 1 < n) (hP : p.Prime) (hp' : p ≠ 2)
    (hpdvd : p ∣ 2 ^ (2 ^ n) + 1) :
    ∃ k, p = k * 2 ^ (n + 2) + 1 := by
  haveI hp := Fact.mk hP
  have h₀ : 2 ^ (2 ^ n) = (-1 : ZMod p) := by
    have : 2 ^ (2 ^ n) + 1 = (0 : ZMod p) := by
      exact_mod_cast (natCast_zmod_eq_zero_iff_dvd (2 ^ (2 ^ n) + 1) p).mpr hpdvd
    exact Eq.symm (neg_eq_of_add_eq_zero_left this)
  have h₁ : 2 ^ (2 ^ (n + 1)) = (1 : ZMod p) := by
    exact Mathlib.Tactic.Ring.pow_nat rfl h₀ neg_one_sq
  have h2ne0 : (0 : ZMod p) ≠ (2 : ZMod p) := by
    let h' := intCast_eq_intCast_iff_dvd_sub 0 2 p
    norm_cast at h'
    rw [ne_eq, h']
    have : Int.subNatNat 2 0 = 2 := rfl
    rw [this]
    norm_cast
    by_contra h''
    apply le_of_dvd at h''
    · have : 2 ≤ p := Prime.two_le hP
      omega
    · norm_num
  have h1neneg : (1 : ZMod p) ≠ (-1 : ZMod p) := by
    by_contra h'
    rcases (neg_eq_self_iff (1 : ZMod p)).mp h'.symm with h | h
    · absurd h
      exact one_ne_zero
    · absurd h
      exact val_one p ▸ Ne.symm hp'
  have h₂ : 2 ^ (n + 1) ∣ p - 1 := by
    have : orderOf (2 : ZMod p) = 2 ^ (n + 1) := by
      apply orderOf_eq_prime_pow
      · rw [h₀, ← ne_eq]
        exact Ne.symm h1neneg
      · exact h₁
    exact this ▸ orderOf_dvd_card_sub_one h2ne0.symm
  have hpmod8 : p % 8 = 1 := by
    have : 8 ∣ p - 1 := by
      apply dvd_trans (a := 8) (b := 2 ^ (n + 1)) (c := p - 1)
      · use 2 ^ (n - 2)
        have : 8 = 2 ^ 3 := by norm_num
        rw [this, Eq.symm (pow_add 2 3 (n - 2)), pow_right_inj]
        all_goals omega
      · exact h₂
    have : 1 ≤ p := NeZero.one_le
    omega
  have hsq : IsSquare (2 : ZMod p) :=
      (exists_sq_eq_two_iff hp').mpr (Or.intro_left (p % 8 = 7) hpmod8)
  have hsqex : ∃ m : ZMod p, m ^ 2 = (2 : ZMod p) := by
    obtain ⟨c, hsq'⟩ := IsSquare.exists_sq (2 : ZMod p) hsq
    use c
    exact Eq.symm hsq'
  have hOrd_dvd (a : ZMod p) (ha : a ^ 2 = (2 : ZMod p)) : 2 ^ (n + 2) ∣ p - 1 := by
    have hOrd : orderOf (a : ZMod p) = 2 ^ (n + 2) := by
      have : a ^ (2 ^ (n + 2)) = (1 : ZMod p) := by
        have : 2 = 1 + 1 := rfl
        nth_rw 2 [this]
        rw [← add_assoc, pow_succ', pow_mul a 2]
        exact ha ▸ h₁
      apply orderOf_eq_prime_pow
      · rw [← ha] at h₀
        rw [pow_succ', pow_mul a 2, h₀]
        exact Ne.symm h1neneg
      · exact this
    rw [← hOrd]
    apply orderOf_dvd_card_sub_one
    contrapose! ha
    rw [ha, ne_eq, zero_pow]
    · exact h2ne0
    · norm_num
  have : ∃ k : ℕ, p - 1 = k * 2 ^ (n + 2) := by
    apply exists_eq_mul_left_of_dvd
    obtain ⟨w, h⟩ := hsqex
    apply hOrd_dvd
    · exact h
  rcases this with ⟨k', h'⟩
  use k'
  rw [← h']
  omega

/-- Prime factors of `Fₙ = 2 ^ (2 ^ n) + 1` are either 3, 5, or of form `k * 2 ^ (n + 2) + 1`. -/
lemma fermat_primeFactors (n p : ℕ) (hP : p.Prime) (hp' : p ≠ 2)
    (hpdvd : p ∣ 2 ^ (2 ^ n) + 1) :
    p = 3 ∨ p = 5 ∨ ∃ k, p = k * 2 ^ (n + 2) + 1 := by
  have : n = 0 ∨ n = 1 ∨ 1 < n := by omega
  rcases this with h | ⟨h | h⟩
  · left

    rw [h] at hpdvd
    exact (Nat.prime_dvd_prime_iff_eq hP prime_three).mp hpdvd
  · right; left
    rw [h] at hpdvd
    norm_num at hpdvd
    exact (Nat.prime_dvd_prime_iff_eq hP prime_five).mp hpdvd
  · right; right
    exact fermat_primeFactors_one_lt n p h hP hp' hpdvd

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
