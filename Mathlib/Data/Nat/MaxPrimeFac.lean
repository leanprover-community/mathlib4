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

## Implementation notes

The list `n.primeFactorsList` is empty exactly when `n = 0` or `n = 1`. Since `Nat.maxPrimeFac`
uses `List.getLastD` with `n` as the default, it returns `n` itself at these exceptional inputs.

The two unconditional laws pin both of these values down, leaving no freedom:

* `maxPrimeFac n ∣ n` is vacuous at `n = 0`, since every natural number divides zero, but it
  forces `maxPrimeFac 1 = 1`, since `1` has no other divisor.
* `maxPrimeFac n ≤ n` forces `maxPrimeFac 0 = 0`, but permits either `0` or `1` at `n = 1`.

Neither law alone determines both points; together they admit exactly one solution, namely
returning `n` when the factor list is empty. This is a single rule rather than two independent
choices, and it is what `List.getLastD` with default `n` computes. The characterization
`maxPrimeFac_eq_self_iff : maxPrimeFac n = n ↔ n ≤ 1 ∨ n.Prime` follows from it.

Choosing `maxPrimeFac 1 = 0` instead would make the `IsLUB` result below and
`maxPrimeFac_eq_sSup` hold unconditionally, since no prime divides `1` and both
`IsLUB ∅ 0` and `sSup ∅ = 0` hold in `ℕ`. That would cost `maxPrimeFac 1 ∣ 1`, and
divisibility is the more useful of the two laws, so it is not taken.

At `n = 0` the value does agree with `maxPrimeFac_eq_sSup`, but only because `ℕ`
totalizes `sSup`: the prime divisors of zero are unbounded, so their supremum is `0` by
convention rather than by being a genuine least upper bound.

For `n > 1` the list `n.primeFactorsList` is nonempty, so the default is never used.
-/

@[expose] public section

namespace Nat

variable {m n : ℕ}

/-- The greatest prime divisor of a natural number `n > 1`.

At the exceptional inputs `n = 0` and `n = 1`, it returns the explicit default `n` because
`n.primeFactorsList` is empty. -/
def maxPrimeFac (n : ℕ) : ℕ := n.primeFactorsList.getLastD n

@[simp] lemma maxPrimeFac_zero : maxPrimeFac 0 = 0 := by simp [maxPrimeFac]
@[simp] lemma maxPrimeFac_one : maxPrimeFac 1 = 1 := by simp [maxPrimeFac]

lemma prime_maxPrimeFac_of_one_lt {n : ℕ} (h : 1 < n) : n.maxPrimeFac.Prime := by
  have : n.primeFactorsList ≠ [] := by simp; lia
  simpa [maxPrimeFac, List.getLast?_eq_getLast_of_ne_nil this]
    using prime_of_mem_primeFactorsList <| List.getLast_mem _

/-- The greatest prime factor of a natural number divides it. -/
lemma maxPrimeFac_dvd : ∀ {n : ℕ}, maxPrimeFac n ∣ n
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by
    have : (n + 2).primeFactorsList ≠ [] := by simp
    simpa [maxPrimeFac, List.getLast?_eq_getLast_of_ne_nil this]
      using dvd_of_mem_primeFactorsList <| List.getLast_mem _

/-- Every prime factor of a nonzero natural number is at most its greatest prime factor. -/
lemma le_maxPrimeFac {n p : ℕ} (hn : n ≠ 0) (hp : p.Prime) (h_dvd : p ∣ n) :
    p ≤ maxPrimeFac n := by
  have := (mem_primeFactorsList hn).2 ⟨hp, h_dvd⟩
  simpa [maxPrimeFac, List.getLast?_eq_getLast_of_ne_nil <| List.ne_nil_of_mem this]
    using (primeFactorsList_sorted n).pairwise.rel_getLast this

lemma maxPrimeFac_eq_of_dvd_of_le (n p : ℕ) (hn : 0 < n) (hp : p.Prime) (h_dvd : p ∣ n)
    (h_le : maxPrimeFac n ≤ p) : maxPrimeFac n = p :=
  le_antisymm h_le (le_maxPrimeFac hn.ne' hp h_dvd)

/-- The greatest prime factor of a prime is the prime itself. -/
@[simp]
lemma Prime.maxPrimeFac_eq_self {p : ℕ} (hp : p.Prime) : maxPrimeFac p = p := by
  apply maxPrimeFac_eq_of_dvd_of_le p p hp.pos hp (dvd_refl p)
  exact Nat.le_of_dvd hp.pos maxPrimeFac_dvd

/-- The fixed points of `maxPrimeFac` are zero, one, and the primes. -/
@[simp]
lemma maxPrimeFac_eq_self_iff {n : ℕ} : maxPrimeFac n = n ↔ n ≤ 1 ∨ n.Prime := by
  constructor
  · intro h
    by_cases hn : n ≤ 1
    · exact Or.inl hn
    · exact Or.inr <| h ▸ prime_maxPrimeFac_of_one_lt (lt_of_not_ge hn)
  · rintro (hn | hn)
    · obtain rfl | rfl := Nat.le_one_iff_eq_zero_or_eq_one.mp hn <;> simp
    · exact hn.maxPrimeFac_eq_self

/-- The greatest prime factor of a natural number greater than one is the greatest of its prime
factors. -/
lemma isGreatest_maxPrimeFac {n : ℕ} (hn : 1 < n) :
    IsGreatest {p : ℕ | p.Prime ∧ p ∣ n} (maxPrimeFac n) :=
  ⟨⟨prime_maxPrimeFac_of_one_lt hn, maxPrimeFac_dvd⟩,
    fun _ hp => le_maxPrimeFac (zero_lt_of_lt hn).ne' hp.1 hp.2⟩

/-- The greatest prime factor of a natural number greater than one is the least upper bound of
its prime factors. -/
lemma isLUB_maxPrimeFac {n : ℕ} (hn : 1 < n) :
    IsLUB {p : ℕ | p.Prime ∧ p ∣ n} (maxPrimeFac n) :=
  (isGreatest_maxPrimeFac hn).isLUB

@[simp]
lemma one_le_maxPrimeFac_iff : ∀ {n : ℕ}, 1 ≤ maxPrimeFac n ↔ 1 ≤ n
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by simpa using (prime_maxPrimeFac_of_one_lt <| by lia).one_lt.le

lemma maxPrimeFac_le_iff (hn : 1 < n) :
    n.maxPrimeFac ≤ m ↔ ∀ p, p.Prime → p ∣ n → p ≤ m := by
  simp [isLUB_le_iff <| isLUB_maxPrimeFac hn, upperBounds]

/-- The greatest prime factor of a product of nonzero natural numbers is the maximum of their
greatest prime factors. -/
lemma maxPrimeFac_mul (hm : m ≠ 0) (hn : n ≠ 0) :
    maxPrimeFac (m * n) = max (maxPrimeFac m) (maxPrimeFac n) := by
  obtain rfl | hm : m = 1 ∨ 1 < m := by lia
  · simp
    lia
  obtain rfl | hn : n = 1 ∨ 1 < n := by lia
  · simp
    lia
  refine eq_of_forall_ge_iff fun c ↦ ?_
  simp +contextual [maxPrimeFac_le_iff, one_lt_mul'' hm hn, Nat.Prime.dvd_mul, or_imp,
    forall_and, *]

/-- The greatest prime factor of a power with nonzero exponent is the greatest prime factor of
its base. -/
@[simp]
lemma maxPrimeFac_pow : ∀ {k : ℕ}, k ≠ 0 → ∀ n, maxPrimeFac (n ^ k) = maxPrimeFac n
  | k + 1, _, 0 => by simp
  | 1, _, n => by simp
  | k + 2, _, n + 1 => by
    rw [pow_succ, maxPrimeFac_mul (pow_ne_zero _ (by lia)) (by lia), maxPrimeFac_pow (by lia)]
    simp

/-- The greatest prime factor of a natural number is at most that number. -/
lemma maxPrimeFac_le : ∀ {n : ℕ}, maxPrimeFac n ≤ n
  | 0 => by simp
  | 1 => by simp
  | n + 2 => Nat.le_of_dvd (by lia) maxPrimeFac_dvd

/-- Away from `n = 1`, the computable greatest prime factor agrees with its supremum
characterization. -/
lemma maxPrimeFac_eq_sSup {n : ℕ} (hn_one : n ≠ 1) :
    maxPrimeFac n = sSup {p : ℕ | p.Prime ∧ p ∣ n} := by
  obtain rfl | hn : n = 0 ∨ 1 < n := by lia
  · simpa using (Set.Infinite.Nat.sSup_eq_zero infinite_setOfPred_prime).symm
  · exact ((isLUB_maxPrimeFac hn).csSup_eq ⟨_, (isGreatest_maxPrimeFac hn).1⟩).symm

@[simp]
lemma one_lt_maxPrimeFac_iff : ∀ {n : ℕ}, 1 < maxPrimeFac n ↔ 1 < n
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by simpa using (prime_maxPrimeFac_of_one_lt <| by lia).one_lt

end Nat
