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

This file defines `Nat.maxFac`, the greatest prime factor of a natural number greater than
one, with explicit values at zero and one.

The list `n.primeFactorsList` is empty exactly when `n = 0` or `n = 1`. Since `Nat.maxFac` uses
`List.getLastD` with `n` as the default, it returns `n` itself at these exceptional inputs.

These default values are chosen so that:

* `maxFac 0 = 0` is the only value compatible with the global bound `maxFac n ≤ n`; it also agrees
  with the natural-number supremum characterization below, since the set of prime divisors of zero
  is unbounded and therefore has `sSup` equal to zero.
* `maxFac 1 = 1` makes the multiplicative identity a fixed point.
* For `n > 1`, `n.primeFactorsList` is nonempty, so the default is never used.
-/

@[expose] public section

namespace Nat

/-- The greatest prime divisor of a natural number `n > 1`.

At the exceptional inputs `n = 0` and `n = 1`, it returns the explicit default `n` because
`n.primeFactorsList` is empty. -/
def maxFac (n : ℕ) : ℕ := n.primeFactorsList.getLastD n

@[simp]
lemma maxFac_zero : maxFac 0 = 0 := by
  simp [maxFac]

@[simp]
lemma maxFac_one : maxFac 1 = 1 := by
  simp [maxFac]

lemma prime_maxFac_of_one_lt (n : ℕ) (h : 1 < n) : Prime (maxFac n) := by
  have hn : n.primeFactorsList ≠ [] := (primeFactorsList_ne_nil n).2 h
  have hmem : n.primeFactorsList.getLast hn ∈ n.primeFactorsList := List.getLast_mem hn
  have hprime : Prime (n.primeFactorsList.getLast hn) := prime_of_mem_primeFactorsList hmem
  simpa [maxFac, List.getLast?_eq_getLast_of_ne_nil hn] using hprime

/-- The greatest prime factor of a natural number divides it. -/
lemma maxFac_dvd : ∀ {n : ℕ}, maxFac n ∣ n
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
    simpa [maxFac, List.getLast?_eq_getLast_of_ne_nil hlist] using hdvd

/-- Every prime factor of a nonzero natural number is at most its greatest prime factor. -/
lemma le_maxFac {n p : ℕ} (hn : n ≠ 0) (hp : p.Prime) (h_dvd : p ∣ n) : p ≤ maxFac n := by
  have hmem : p ∈ n.primeFactorsList := (mem_primeFactorsList hn).2 ⟨hp, h_dvd⟩
  have hlist : n.primeFactorsList ≠ [] := List.ne_nil_of_mem hmem
  have hp_last : p ≤ n.primeFactorsList.getLast hlist :=
    (primeFactorsList_sorted n).pairwise.rel_getLast hmem
  simpa [maxFac, List.getLast?_eq_getLast_of_ne_nil hlist] using hp_last

lemma maxFac_eq_of_dvd_of_le (n p : ℕ) (hn : 0 < n) (hp : p.Prime) (h_dvd : p ∣ n)
    (h_le : maxFac n ≤ p) : maxFac n = p := by
  exact le_antisymm h_le (le_maxFac hn.ne' hp h_dvd)

/-- The greatest prime factor of a prime is the prime itself. -/
@[simp]
lemma Prime.maxFac_eq_self {p : ℕ} (hp : p.Prime) : maxFac p = p := by
  apply maxFac_eq_of_dvd_of_le p p hp.pos hp (dvd_refl p)
  exact Nat.le_of_dvd hp.pos maxFac_dvd

/-- The fixed points of `maxFac` are zero, one, and the primes. -/
@[simp]
lemma maxFac_eq_self_iff {n : ℕ} : maxFac n = n ↔ n ≤ 1 ∨ n.Prime := by
  constructor
  · intro h
    by_cases hn : n ≤ 1
    · exact Or.inl hn
    · exact Or.inr <| h ▸ prime_maxFac_of_one_lt n (lt_of_not_ge hn)
  · rintro (hn | hn)
    · obtain rfl | rfl := Nat.le_one_iff_eq_zero_or_eq_one.mp hn <;> simp
    · exact hn.maxFac_eq_self

/-- The greatest prime factor of a product of nonzero natural numbers is the maximum of their
greatest prime factors. -/
lemma maxFac_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    maxFac (m * n) = max (maxFac m) (maxFac n) := by
  obtain rfl | hm_lt : m = 1 ∨ 1 < m := by omega
  · have hle : 1 ≤ maxFac n := by
      obtain rfl | hn_lt : n = 1 ∨ 1 < n := by omega
      · simp
      · exact (prime_maxFac_of_one_lt n hn_lt).one_lt.le
    simp [hle]
  obtain rfl | hn_lt : n = 1 ∨ 1 < n := by omega
  · have hle : 1 ≤ maxFac m := (prime_maxFac_of_one_lt m hm_lt).one_lt.le
    simp [hle]
  have hmn_lt : 1 < m * n := Nat.one_lt_mul_iff.mpr
    ⟨zero_lt_of_lt hm_lt, zero_lt_of_lt hn_lt, Or.inl hm_lt⟩
  apply le_antisymm
  · have hp : Prime (maxFac (m * n)) := prime_maxFac_of_one_lt (m * n) hmn_lt
    rcases hp.dvd_mul.mp maxFac_dvd with hpm | hpn
    · exact (le_maxFac hm hp hpm).trans (le_max_left _ _)
    · exact (le_maxFac hn hp hpn).trans (le_max_right _ _)
  · apply max_le
    · have hp : Prime (maxFac m) := prime_maxFac_of_one_lt m hm_lt
      apply le_maxFac (mul_ne_zero hm hn) hp
      exact dvd_mul_of_dvd_left maxFac_dvd n
    · have hp : Prime (maxFac n) := prime_maxFac_of_one_lt n hn_lt
      apply le_maxFac (mul_ne_zero hm hn) hp
      exact dvd_mul_of_dvd_right maxFac_dvd m

/-- The greatest prime factor of a nonzero power is the greatest prime factor of its base. -/
@[simp]
lemma maxFac_pow {k : ℕ} (hk : k ≠ 0) (n : ℕ) : maxFac (n ^ k) = maxFac n :=
  match k, hk with
  | k + 1, _ => by
    by_cases hn : n = 0
    · subst n
      simp
    induction k with
    | zero => simp
    | succ k ih =>
        rw [pow_succ, maxFac_mul (pow_ne_zero _ hn) hn, ih (by omega)]
        simp

/-- The greatest prime factor of a natural number is at most that number. -/
lemma maxFac_le : ∀ {n : ℕ}, maxFac n ≤ n
  | 0 => by simp
  | 1 => by simp
  | n + 2 => Nat.le_of_dvd (by omega) maxFac_dvd

/-- The greatest prime factor of a natural number greater than one is the least upper bound of
its prime factors. -/
lemma isLeast_maxFac {n : ℕ} (hn : 1 < n) :
    IsLeast (upperBounds {p : ℕ | p.Prime ∧ p ∣ n}) (maxFac n) := by
  constructor
  · rintro p ⟨hp, h_dvd⟩
    exact le_maxFac (zero_lt_of_lt hn).ne' hp h_dvd
  · intro b hb
    exact hb ⟨prime_maxFac_of_one_lt n hn, maxFac_dvd⟩

/-- Away from `n = 1`, the computable greatest prime factor agrees with its supremum
characterization. -/
lemma maxFac_eq_sSup {n : ℕ} (hn_one : n ≠ 1) :
    maxFac n = sSup {p : ℕ | p.Prime ∧ p ∣ n} := by
  obtain rfl | hn : n = 0 ∨ 1 < n := by lia
  · simpa using (Set.Infinite.Nat.sSup_eq_zero infinite_setOfPred_prime).symm
  · have h_lub : IsLUB {p : ℕ | p.Prime ∧ p ∣ n} (maxFac n) :=
      isLeast_maxFac hn
    exact (h_lub.csSup_eq
      ⟨maxFac n, prime_maxFac_of_one_lt n hn, maxFac_dvd⟩).symm

@[simp]
lemma one_lt_maxFac_iff (n : ℕ) : 1 < maxFac n ↔ 1 < n := by
  rcases lt_trichotomy n 1 with hn | rfl | hn
  · simp only [lt_one_iff] at hn
    simp [hn]
  · simp
  · simpa [hn] using (prime_maxFac_of_one_lt n hn).one_lt

end Nat
