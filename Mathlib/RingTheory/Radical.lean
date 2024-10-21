/-
Copyright (c) 2024 Jineon Baek, Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jineon Baek, Seewoo Lee
-/
import Mathlib.RingTheory.UniqueFactorizationDomain

/-!
# Radical of an element of a unique factorization normalization monoid

This file defines a radical of an element `a` of a unique factorization normalization
monoid, which is defined as a product of normalized prime factors of `a` without duplication.
This is different from the radical of an ideal.

## Main declarations

- `radical`: The radical of an element `a` in a unique factorization monoid is the product of
  its prime factors.
- `radical_eq_of_associated`: If `a` and `b` are associates, i.e. `a * u = b` for some unit `u`,
  then `radical a = radical b`.
- `radical_unit_mul`: Multiplying unit does not change the radical.
- `radical_dvd_self`: `radical a` divides `a`.
- `radical_pow`: `radical (a ^ n) = radical a` for any `n ≥ 1`
- `radical_of_prime`: Radical of a prime element is equal to its normalization
- `radical_pow_of_prime`: Radical of a power of prime element is equal to its normalization

## TODO

- Make a comparison with `Ideal.radical`. Especially, for principal ideal,
  `Ideal.radical (Ideal.span {a}) = Ideal.span {radical a}`.
- Prove `radical (radical a) = radical a`.
- Prove a comparison between `primeFactors` and `Nat.primeFactors`.
-/

noncomputable section

open scoped Classical

namespace UniqueFactorizationMonoid

-- `CancelCommMonoidWithZero` is required by `UniqueFactorizationMonoid`
variable {M : Type*} [CancelCommMonoidWithZero M] [NormalizationMonoid M]
  [UniqueFactorizationMonoid M]

/-- The finite set of prime factors of an element in a unique factorization monoid. -/
def primeFactors (a : M) : Finset M :=
  (normalizedFactors a).toFinset

theorem _root_.Associated.primeFactors_eq {a b : M} (h : Associated a b) :
    primeFactors a = primeFactors b := by
  unfold primeFactors
  rw [h.normalizedFactors_eq]


/--
Radical of an element `a` in a unique factorization monoid is the product of
the prime factors of `a`.
-/
def radical (a : M) : M :=
  (primeFactors a).prod id

@[simp]
theorem radical_zero_eq : radical (0 : M) = 1 := by
  rw [radical, primeFactors, normalizedFactors_zero, Multiset.toFinset_zero, Finset.prod_empty]

@[simp]
theorem radical_one_eq : radical (1 : M) = 1 := by
  rw [radical, primeFactors, normalizedFactors_one, Multiset.toFinset_zero, Finset.prod_empty]

theorem radical_eq_of_associated {a b : M} (h : Associated a b) : radical a = radical b := by
  unfold radical
  rw [h.primeFactors_eq]

theorem radical_unit_eq_one {a : M} (h : IsUnit a) : radical a = 1 :=
  (radical_eq_of_associated (associated_one_iff_isUnit.mpr h)).trans radical_one_eq

theorem radical_unit_mul {u : Mˣ} {a : M} : radical ((↑u : M) * a) = radical a :=
  radical_eq_of_associated (associated_unit_mul_left _ _ u.isUnit)

theorem radical_mul_unit {u : Mˣ} {a : M} : radical (a * (↑u : M)) = radical a :=
  radical_eq_of_associated (associated_mul_unit_left _ _ u.isUnit)

theorem primeFactors_pow (a : M) {n : ℕ} (hn : 0 < n) : primeFactors (a ^ n) = primeFactors a := by
  simp_rw [primeFactors]
  simp only [normalizedFactors_pow]
  rw [Multiset.toFinset_nsmul]
  exact ne_of_gt hn

theorem radical_pow (a : M) {n : Nat} (hn : 0 < n) : radical (a ^ n) = radical a := by
  simp_rw [radical, primeFactors_pow a hn]

theorem radical_dvd_self (a : M) : radical a ∣ a := by
  by_cases ha : a = 0
  · rw [ha]
    apply dvd_zero
  · rw [radical, ← Finset.prod_val, ← (normalizedFactors_prod ha).dvd_iff_dvd_right]
    apply Multiset.prod_dvd_prod_of_le
    rw [primeFactors, Multiset.toFinset_val]
    apply Multiset.dedup_le

theorem radical_of_prime {a : M} (ha : Prime a) : radical a = normalize a := by
  rw [radical, primeFactors]
  rw [normalizedFactors_irreducible ha.irreducible]
  simp only [Multiset.toFinset_singleton, id, Finset.prod_singleton]

theorem radical_pow_of_prime {a : M} (ha : Prime a) {n : ℕ} (hn : 0 < n) :
    radical (a ^ n) = normalize a := by
  rw [radical_pow a hn]
  exact radical_of_prime ha

theorem radical_ne_zero (a : M) [Nontrivial M] : radical a ≠ 0 := by
  rw [radical, ← Finset.prod_val]
  apply Multiset.prod_ne_zero
  rw [primeFactors]
  simp only [Multiset.toFinset_val, Multiset.mem_dedup]
  exact zero_not_mem_normalizedFactors _

end UniqueFactorizationMonoid

open UniqueFactorizationMonoid

namespace UniqueFactorizationDomain
-- Theorems for UFDs

variable {R : Type*} [CommRing R] [IsDomain R] [NormalizationMonoid R]
  [UniqueFactorizationMonoid R]

/-- Coprime elements have disjoint prime factors (as multisets). -/
theorem disjoint_normalizedFactors {a b : R} (hc : IsCoprime a b) :
    (normalizedFactors a).Disjoint (normalizedFactors b) := by
  intro x hxa hxb
  have x_dvd_a := dvd_of_mem_normalizedFactors hxa
  have x_dvd_b := dvd_of_mem_normalizedFactors hxb
  have xp := prime_of_normalized_factor x hxa
  exact xp.not_unit (hc.isUnit_of_dvd' x_dvd_a x_dvd_b)

/-- Coprime elements have disjoint prime factors (as finsets). -/
theorem disjoint_primeFactors {a b : R} (hc : IsCoprime a b) :
    Disjoint (primeFactors a) (primeFactors b) :=
  Multiset.disjoint_toFinset.mpr (disjoint_normalizedFactors hc)

theorem mul_primeFactors_disjUnion {a b : R} (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : IsCoprime a b) :
    primeFactors (a * b) =
    (primeFactors a).disjUnion (primeFactors b) (disjoint_primeFactors hc) := by
  rw [Finset.disjUnion_eq_union]
  simp_rw [primeFactors]
  rw [normalizedFactors_mul ha hb, Multiset.toFinset_add]

@[simp]
theorem radical_neg_one : radical (-1 : R) = 1 :=
  radical_unit_eq_one isUnit_one.neg

/-- Radical is multiplicative for coprime elements. -/
theorem radical_mul {a b : R} (hc : IsCoprime a b) :
    radical (a * b) = (radical a) * (radical b) := by
  by_cases ha : a = 0
  · subst ha; rw [isCoprime_zero_left] at hc
    simp only [zero_mul, radical_zero_eq, one_mul, radical_unit_eq_one hc]
  by_cases hb : b = 0
  · subst hb; rw [isCoprime_zero_right] at hc
    simp only [mul_zero, radical_zero_eq, mul_one, radical_unit_eq_one hc]
  simp_rw [radical]
  rw [mul_primeFactors_disjUnion ha hb hc]
  rw [Finset.prod_disjUnion (disjoint_primeFactors hc)]

theorem radical_neg {a : R} : radical (-a) = radical a :=
  radical_eq_of_associated Associated.rfl.neg_left

end UniqueFactorizationDomain
