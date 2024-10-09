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
  rcases iff_iff_and_or_not_and_not.mp h.eq_zero_iff with (⟨rfl, rfl⟩ | ⟨ha, hb⟩)
  · rfl
  · simp_rw [radical, primeFactors]
    rw [(associated_iff_normalizedFactors_eq_normalizedFactors ha hb).mp h]

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

end UniqueFactorizationMonoid
