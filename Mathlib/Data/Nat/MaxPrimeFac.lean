/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.Order.Lattice.Nat

/-!
# Greatest prime factor of a natural number

This file defines `Nat.maxPrimeFac`, the greatest prime factor of a natural number greater than
one, with explicit values at zero and one.
-/

@[expose] public section

namespace Nat

/-- The greatest prime divisor of a natural number `n > 1`.

Takes the junk value `0` for `n = 0` and `1` for `n = 1`. -/
def maxPrimeFac (n : ℕ) : ℕ := if n = 1 then 1 else n.primeFactorsList.getLastI

@[simp]
lemma maxPrimeFac_zero :
    maxPrimeFac 0 = 0 := by
  simp [maxPrimeFac, List.getLastI]

@[simp]
lemma maxPrimeFac_one :
    maxPrimeFac 1 = 1 := rfl

lemma prime_maxPrimeFac_of_one_lt (n : ℕ) (h : 1 < n) :
    Prime (maxPrimeFac n) := by
  have hn : n.primeFactorsList ≠ [] := (primeFactorsList_ne_nil n).2 h
  have hmem : n.primeFactorsList.getLast hn ∈ n.primeFactorsList := List.getLast_mem hn
  have hprime : Prime (n.primeFactorsList.getLast hn) := prime_of_mem_primeFactorsList hmem
  simpa [maxPrimeFac, h.ne', List.getLastI_eq_getLast?_getD,
    List.getLast?_eq_getLast_of_ne_nil hn] using hprime

/-- The greatest prime factor of a natural number divides it. -/
lemma maxPrimeFac_dvd : ∀ {n : ℕ}, maxPrimeFac n ∣ n
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by
    have hn : 1 < n + 2 := by omega
    have hlist : (n + 2).primeFactorsList ≠ [] :=
      (primeFactorsList_ne_nil (n + 2)).2 hn
    have hmem : (n + 2).primeFactorsList.getLast hlist ∈ (n + 2).primeFactorsList :=
      List.getLast_mem hlist
    have hdvd : (n + 2).primeFactorsList.getLast hlist ∣ n + 2 :=
      dvd_of_mem_primeFactorsList hmem
    simpa [maxPrimeFac, hn.ne', List.getLastI_eq_getLast?_getD,
      List.getLast?_eq_getLast_of_ne_nil hlist] using hdvd

/-- Every prime factor of a nonzero natural number is at most its greatest prime factor. -/
lemma le_maxPrimeFac
    {n p : ℕ} (hn : n ≠ 0) (hp : p.Prime) (h_dvd : p ∣ n) :
    p ≤ maxPrimeFac n := by
  have hmem : p ∈ n.primeFactorsList := (mem_primeFactorsList hn).2 ⟨hp, h_dvd⟩
  have hlist : n.primeFactorsList ≠ [] := List.ne_nil_of_mem hmem
  have hn_one : n ≠ 1 := ((primeFactorsList_ne_nil n).1 hlist).ne'
  have hp_last : p ≤ n.primeFactorsList.getLast hlist :=
    (primeFactorsList_sorted n).pairwise.rel_getLast hmem
  simpa [maxPrimeFac, hn_one, List.getLastI_eq_getLast?_getD,
    List.getLast?_eq_getLast_of_ne_nil hlist] using hp_last

lemma maxPrimeFac_eq_of_dvd_of_le
    (n p : ℕ) (hn : 0 < n) (hp : p.Prime) (h_dvd : p ∣ n) (h_le : maxPrimeFac n ≤ p) :
    maxPrimeFac n = p := by
  exact le_antisymm h_le (le_maxPrimeFac hn.ne' hp h_dvd)

/-- The greatest prime factor of a prime is the prime itself. -/
@[simp]
lemma Prime.maxPrimeFac_eq_self {p : ℕ} (hp : p.Prime) :
    maxPrimeFac p = p := by
  apply maxPrimeFac_eq_of_dvd_of_le p p hp.pos hp (dvd_refl p)
  exact Nat.le_of_dvd hp.pos maxPrimeFac_dvd

/-- The fixed points of `maxPrimeFac` are zero, one, and the primes. -/
@[simp]
lemma maxPrimeFac_eq_self_iff {n : ℕ} :
    maxPrimeFac n = n ↔ n ≤ 1 ∨ n.Prime := by
  constructor
  · intro h
    by_cases hn : n ≤ 1
    · exact Or.inl hn
    · exact Or.inr <| h ▸ prime_maxPrimeFac_of_one_lt n (lt_of_not_ge hn)
  · rintro (hn | hn)
    · obtain rfl | rfl := Nat.le_one_iff_eq_zero_or_eq_one.mp hn <;> simp
    · exact hn.maxPrimeFac_eq_self

/-- The greatest prime factor of a product of nonzero natural numbers is the maximum of their
greatest prime factors. -/
lemma maxPrimeFac_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    maxPrimeFac (m * n) = max (maxPrimeFac m) (maxPrimeFac n) := by
  obtain rfl | hm_lt : m = 1 ∨ 1 < m := by omega
  · have hle : 1 ≤ maxPrimeFac n := by
      obtain rfl | hn_lt : n = 1 ∨ 1 < n := by omega
      · simp
      · exact (prime_maxPrimeFac_of_one_lt n hn_lt).one_lt.le
    simp [hle]
  obtain rfl | hn_lt : n = 1 ∨ 1 < n := by omega
  · have hle : 1 ≤ maxPrimeFac m := (prime_maxPrimeFac_of_one_lt m hm_lt).one_lt.le
    simp [hle]
  have hmn_lt : 1 < m * n := Nat.one_lt_mul_iff.mpr
    ⟨zero_lt_of_lt hm_lt, zero_lt_of_lt hn_lt, Or.inl hm_lt⟩
  apply le_antisymm
  · have hp : Prime (maxPrimeFac (m * n)) := prime_maxPrimeFac_of_one_lt (m * n) hmn_lt
    rcases hp.dvd_mul.mp maxPrimeFac_dvd with hpm | hpn
    · exact (le_maxPrimeFac hm hp hpm).trans (le_max_left _ _)
    · exact (le_maxPrimeFac hn hp hpn).trans (le_max_right _ _)
  · apply max_le
    · have hp : Prime (maxPrimeFac m) := prime_maxPrimeFac_of_one_lt m hm_lt
      apply le_maxPrimeFac (mul_ne_zero hm hn) hp
      exact dvd_mul_of_dvd_left maxPrimeFac_dvd n
    · have hp : Prime (maxPrimeFac n) := prime_maxPrimeFac_of_one_lt n hn_lt
      apply le_maxPrimeFac (mul_ne_zero hm hn) hp
      exact dvd_mul_of_dvd_right maxPrimeFac_dvd m

/-- The greatest prime factor of a nonzero power is the greatest prime factor of its base. -/
@[simp]
lemma maxPrimeFac_pow {k : ℕ} (hk : k ≠ 0) (n : ℕ) :
    maxPrimeFac (n ^ k) = maxPrimeFac n :=
  match k, hk with
  | k + 1, _ => by
    by_cases hn : n = 0
    · subst n
      simp
    induction k with
    | zero => simp
    | succ k ih =>
        rw [pow_succ, maxPrimeFac_mul (pow_ne_zero _ hn) hn, ih (by omega)]
        simp

/-- The greatest prime factor of a natural number is at most that number. -/
lemma maxPrimeFac_le : ∀ {n : ℕ}, maxPrimeFac n ≤ n
  | 0 => by simp
  | 1 => by simp
  | n + 2 => Nat.le_of_dvd (by omega) maxPrimeFac_dvd

/-- The greatest prime factor of a natural number greater than one is the least upper bound of
its prime factors. -/
lemma isLeast_maxPrimeFac {n : ℕ} (hn : 1 < n) :
    IsLeast (upperBounds {p : ℕ | p.Prime ∧ p ∣ n}) (maxPrimeFac n) := by
  constructor
  · rintro p ⟨hp, h_dvd⟩
    exact le_maxPrimeFac (zero_lt_of_lt hn).ne' hp h_dvd
  · intro b hb
    exact hb ⟨prime_maxPrimeFac_of_one_lt n hn, maxPrimeFac_dvd⟩

/-- Away from `n = 1`, the computable greatest prime factor agrees with its supremum
characterization. -/
lemma maxPrimeFac_eq_sSup {n : ℕ} (hn_one : n ≠ 1) :
    maxPrimeFac n = sSup {p : ℕ | p.Prime ∧ p ∣ n} := by
  obtain rfl | hn : n = 0 ∨ 1 < n := by lia
  · simpa using (Set.Infinite.Nat.sSup_eq_zero infinite_setOfPred_prime).symm
  · have h_lub : IsLUB {p : ℕ | p.Prime ∧ p ∣ n} (maxPrimeFac n) :=
      isLeast_maxPrimeFac hn
    exact (h_lub.csSup_eq
      ⟨maxPrimeFac n, prime_maxPrimeFac_of_one_lt n hn, maxPrimeFac_dvd⟩).symm

@[simp]
lemma one_lt_maxPrimeFac_iff (n : ℕ) :
    1 < maxPrimeFac n ↔ 1 < n := by
  rcases lt_trichotomy n 1 with hn | rfl | hn
  · simp only [lt_one_iff] at hn
    simp [hn]
  · simp
  · simpa [hn] using (prime_maxPrimeFac_of_one_lt n hn).one_lt

end Nat
