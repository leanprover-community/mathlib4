/-
Copyright (c) 2024 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.LucasPrimality

/-!
# Fermat numbers

The Fermat numbers are a sequence of natural numbers defined as `Nat.fermatNumber n = 2^(2^n) + 1`,
for all natural numbers `n`.

## Main theorems

- `Nat.coprime_fermatNumber_fermatNumber`: two distinct Fermat numbers are coprime.
- `Nat.pepin_primality`: For 0 < n, Fermat number Fₙ is prime if `3 ^ (2 ^ (2 ^ n - 1)) = -1 mod Fₙ`
- `fermat_primeFactors_one_lt`: For 1 < n, Prime factors the Fermat number Fₙ are of
  form `k * 2 ^ (n + 2) + 1`.
-/

open Function

namespace Nat

open Finset Nat ZMod
open scoped BigOperators

/-- Fermat numbers: the `n`-th Fermat number is defined as `2^(2^n) + 1`. -/
def fermatNumber (n : ℕ) : ℕ := 2 ^ (2 ^ n) + 1

@[simp] theorem fermatNumber_zero : fermatNumber 0 = 3 := rfl
@[simp] theorem fermatNumber_one : fermatNumber 1 = 5 := rfl
@[simp] theorem fermatNumber_two : fermatNumber 2 = 17 := rfl

theorem fermatNumber_strictMono : StrictMono fermatNumber := by
  intro m n
  simp only [fermatNumber, add_lt_add_iff_right, Nat.pow_lt_pow_iff_right (one_lt_two : 1 < 2),
    imp_self]

lemma fermatNumber_mono : Monotone fermatNumber := fermatNumber_strictMono.monotone
lemma fermatNumber_injective : Injective fermatNumber := fermatNumber_strictMono.injective

lemma three_le_fermatNumber (n : ℕ) : 3 ≤ fermatNumber n := fermatNumber_mono n.zero_le
lemma two_lt_fermatNumber (n : ℕ) : 2 < fermatNumber n := three_le_fermatNumber _

lemma fermatNumber_ne_one (n : ℕ) : fermatNumber n ≠ 1 := by have := three_le_fermatNumber n; omega

theorem odd_fermatNumber (n : ℕ) : Odd (fermatNumber n) :=
  (even_pow.mpr ⟨even_two, (pow_pos two_pos n).ne'⟩).add_one

theorem prod_fermatNumber (n : ℕ) : ∏ k ∈ range n, fermatNumber k = fermatNumber n - 2 := by
  induction n with | zero => rfl | succ n hn =>
  rw [prod_range_succ, hn, fermatNumber, fermatNumber, mul_comm,
    (show 2 ^ 2 ^ n + 1 - 2 = 2 ^ 2 ^ n - 1 by omega), ← sq_sub_sq]
  ring_nf
  omega

theorem fermatNumber_eq_prod_add_two (n : ℕ) :
    fermatNumber n = ∏ k ∈ range n, fermatNumber k + 2 := by
  rw [prod_fermatNumber, Nat.sub_add_cancel]
  exact le_of_lt <| two_lt_fermatNumber _

theorem fermatNumber_succ (n : ℕ) : fermatNumber (n + 1) = (fermatNumber n - 1) ^ 2 + 1 := by
  rw [fermatNumber, pow_succ, mul_comm, pow_mul', fermatNumber, add_tsub_cancel_right]

theorem two_mul_fermatNumber_sub_one_sq_le_fermatNumber_sq (n : ℕ) :
    2 * (fermatNumber n - 1) ^ 2 ≤ (fermatNumber (n + 1)) ^ 2 := by
  simp only [fermatNumber, add_tsub_cancel_right]
  have : 0 ≤ 1 + 2 ^ (2 ^ n * 4) := le_add_left _ _
  ring_nf
  omega

theorem fermatNumber_eq_fermatNumber_sq_sub_two_mul_fermatNumber_sub_one_sq (n : ℕ) :
    fermatNumber (n + 2) = (fermatNumber (n + 1)) ^ 2 - 2 * (fermatNumber n - 1) ^ 2 := by
  simp only [fermatNumber, add_sub_self_right]
  rw [← add_sub_self_right (2 ^ 2 ^ (n + 2) + 1) <| 2 * 2 ^ 2 ^ (n + 1)]
  ring_nf

end Nat

open Nat

theorem Int.fermatNumber_eq_fermatNumber_sq_sub_two_mul_fermatNumber_sub_one_sq (n : ℕ) :
    (fermatNumber (n + 2) : ℤ) = (fermatNumber (n + 1)) ^ 2 - 2 * (fermatNumber n - 1) ^ 2 := by
  rw [Nat.fermatNumber_eq_fermatNumber_sq_sub_two_mul_fermatNumber_sub_one_sq,
    Nat.cast_sub <| two_mul_fermatNumber_sub_one_sq_le_fermatNumber_sq n]
  simp only [fermatNumber, push_cast, add_tsub_cancel_right]

namespace Nat

open Finset
/--
**Goldbach's theorem** : no two distinct Fermat numbers share a common factor greater than one.

From a letter to Euler, see page 37 in [juskevic2022].
-/
theorem coprime_fermatNumber_fermatNumber {m n : ℕ} (hmn : m ≠ n) :
    Coprime (fermatNumber m) (fermatNumber n) := by
  wlog hmn' : m < n
  · simpa only [coprime_comm] using this hmn.symm (by omega)
  let d := (fermatNumber m).gcd (fermatNumber n)
  have h_n : d ∣ fermatNumber n := gcd_dvd_right ..
  have h_m : d ∣ 2 := (Nat.dvd_add_right <| (gcd_dvd_left _ _).trans <| dvd_prod_of_mem _
    <| mem_range.mpr hmn').mp <| fermatNumber_eq_prod_add_two _ ▸ h_n
  refine ((dvd_prime prime_two).mp h_m).resolve_right fun h_two ↦ ?_
  exact (odd_fermatNumber _).not_two_dvd_nat (h_two ▸ h_n)

lemma pairwise_coprime_fermatNumber :
    Pairwise fun m n ↦ Coprime (fermatNumber m) (fermatNumber n) :=
  fun _m _n ↦ coprime_fermatNumber_fermatNumber

open ZMod

/-- Prime `a ^ n + 1` implies `n` is a power of two (**Fermat primes**). -/
theorem pow_of_pow_add_prime {a n : ℕ} (ha : 1 < a) (hn : n ≠ 0) (hP : (a ^ n + 1).Prime) :
    ∃ m : ℕ, n = 2 ^ m := by
  obtain ⟨k, m, hm, rfl⟩ := exists_eq_two_pow_mul_odd hn
  rw [pow_mul] at hP
  use k
  replace ha : 1 < a ^ 2 ^ k := one_lt_pow (pow_ne_zero k two_ne_zero) ha
  let h := hm.nat_add_dvd_pow_add_pow (a ^ 2 ^ k) 1
  rw [one_pow, hP.dvd_iff_eq (Nat.lt_add_right 1 ha).ne', add_left_inj, pow_eq_self_iff ha] at h
  rw [h, mul_one]

/-- `Fₙ = 2^(2^n)+1` is prime if `3^(2^(2^n-1)) = -1 mod Fₙ` (**Pépin's test**). -/
lemma pepin_primality (n : ℕ) (h : 3 ^ (2 ^ (2 ^ n - 1)) = (-1 : ZMod (fermatNumber n))) :
    (fermatNumber n).Prime := by
  have := Fact.mk (two_lt_fermatNumber n)
  have key : 2 ^ n = 2 ^ n - 1 + 1 := (Nat.sub_add_cancel Nat.one_le_two_pow).symm
  apply lucas_primality (p := 2 ^ (2 ^ n) + 1) (a := 3)
  · rw [Nat.add_sub_cancel, key, pow_succ, pow_mul, ← pow_succ, ← key, h, neg_one_sq]
  · intro p hp1 hp2
    rw [Nat.add_sub_cancel, (Nat.prime_dvd_prime_iff_eq hp1 prime_two).mp (hp1.dvd_of_dvd_pow hp2),
        key, pow_succ, Nat.mul_div_cancel _ two_pos, ← pow_succ, ← key, h]
    exact neg_one_ne_one

/-- `Fₙ = 2^(2^n)+1` is prime if `3^((Fₙ - 1)/2) = -1 mod Fₙ` (**Pépin's test**). -/
lemma pepin_primality' (n : ℕ) (h : 3 ^ ((fermatNumber n - 1) / 2) = (-1 : ZMod (fermatNumber n))) :
    (fermatNumber n).Prime := by
  apply pepin_primality
  rw [← h]
  congr
  rw [fermatNumber, add_tsub_cancel_right, Nat.pow_div Nat.one_le_two_pow Nat.zero_lt_two]


/-- Prime factors of `a ^ (2 ^ n) + 1` are of form `k * 2 ^ (n + 1) + 1`. -/
lemma pow_pow_add_primeFactors_one_lt {a n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpdvd : p ∣ a ^ (2 ^ n) + 1) :
    ∃ k, p = k * 2 ^ (n + 1) + 1 := by
  have : Fact (2 < p) := Fact.mk (lt_of_le_of_ne hp.two_le hp2.symm)
  have : Fact p.Prime := Fact.mk hp
  have ha1 : (a : ZMod p) ^ (2 ^ n) = -1 := by
    rw [eq_neg_iff_add_eq_zero]
    exact_mod_cast (natCast_eq_zero_iff (a ^ (2 ^ n) + 1) p).mpr hpdvd
  have ha0 : (a : ZMod p) ≠ 0 := by
    intro h
    rw [h, zero_pow (pow_ne_zero n two_ne_zero), zero_eq_neg] at ha1
    exact one_ne_zero ha1
  have ha : orderOf (a : ZMod p) = 2 ^ (n + 1) := by
    apply orderOf_eq_prime_pow
    · rw [ha1]
      exact neg_one_ne_one
    · rw [pow_succ, pow_mul, ha1, neg_one_sq]
  simpa [ha, dvd_def, Nat.sub_eq_iff_eq_add hp.one_le, mul_comm] using orderOf_dvd_card_sub_one ha0

-- Prime factors of `Fₙ = 2 ^ (2 ^ n) + 1`, `1 < n`, are of form `k * 2 ^ (n + 2) + 1`. -/
lemma fermat_primeFactors_one_lt (n p : ℕ) (hn : 1 < n) (hp : p.Prime)
    (hpdvd : p ∣ fermatNumber n) :
    ∃ k, p = k * 2 ^ (n + 2) + 1 := by
  have : Fact p.Prime := Fact.mk hp
  have hp2 : p ≠ 2 := by
    exact ((even_pow.mpr ⟨even_two, pow_ne_zero n two_ne_zero⟩).add_one).ne_two_of_dvd_nat hpdvd
  have hp8 : p % 8 = 1 := by
    obtain ⟨k, rfl⟩ := pow_pow_add_primeFactors_one_lt hp hp2 hpdvd
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hn
    rw [add_assoc, pow_add, ← mul_assoc, ← mod_add_mod, mul_mod]
    simp
  obtain ⟨a, ha⟩ := (exists_sq_eq_two_iff hp2).mpr (Or.inl hp8)
  suffices h : p ∣ a.val ^ (2 ^ (n + 1)) + 1 by
    exact pow_pow_add_primeFactors_one_lt hp hp2 h
  rw [fermatNumber] at hpdvd
  rw [← natCast_eq_zero_iff, Nat.cast_add _ 1, Nat.cast_one, Nat.cast_pow] at hpdvd ⊢
  rwa [natCast_val, ZMod.cast_id, pow_succ', pow_mul, sq, ← ha]


-- TODO: move to NumberTheory.Mersenne, once we have that.
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
    let h := Nat.sub_dvd_pow_sub_pow a 1 n
    rw [one_pow, hP.dvd_iff_eq (mt (Nat.sub_eq_iff_eq_add ha1.le).mp hn1), eq_comm] at h
    exact (pow_eq_self_iff ha1).mp (Nat.sub_one_cancel ha0 (pow_pos ha0 n) h).symm
  subst ha2
  refine ⟨rfl, Nat.prime_def.mpr ⟨(two_le_iff n).mpr ⟨hn0, hn1⟩, fun d hdn ↦ ?_⟩⟩
  have hinj : ∀ x y, 2 ^ x - 1 = 2 ^ y - 1 → x = y :=
    fun x y h ↦ Nat.pow_right_injective le_rfl (sub_one_cancel (pow_pos ha0 x) (pow_pos ha0 y) h)
  let h := Nat.sub_dvd_pow_sub_pow (2 ^ d) 1 (n / d)
  rw [one_pow, ← pow_mul, Nat.mul_div_cancel' hdn] at h
  exact (hP.eq_one_or_self_of_dvd (2 ^ d - 1) h).imp (hinj d 1) (hinj d n)

end Nat
