/-
Copyright (c) 2024 Jineon Back and Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jineon Baek, Seewoo Lee
-/
import Mathlib.RingTheory.UniqueFactorizationDomain

/-!
# Radical of an element of a unique factorization normalization monoid

This file defines a radical `rad(a)` of an element `a` of a unique factorization normalization
monoid, which is defined as a product of normalized prime factors of `a` without duplication.
This is different from the radical of ideal.

## Main declarations

- `radical_associated_eq`: If `a` and `b` are associates, i.e. `a * u = b` for some unit `u`,
  then `rad(a) = rad(b)`.
- `radical_unit_hMul`: Multiplying unit does not change the radical.
- `radical_dvd_self`: `rad(a)` divides `a`.
- `radical_pow`: `rad(a ^ n) = rad(a)` for any `n ≥ 1`
- `radical_prime`: Radical of a prime element is equal to its normalization

## TODO

- Make a comparison with `Ideal.radical`. Especially, for principal ideal, `rad((a)) = (rad(a))`,
  where the first (resp. second) `rad` is radical of an ideal (resp. element).
- Prove `rad(rad(a)) = rad(a)`.
-/

noncomputable section

open scoped Classical

open UniqueFactorizationMonoid

variable {k : Type _} [Field k]
variable {α : Type _} [CancelCommMonoidWithZero α] [NormalizationMonoid α]
  [UniqueFactorizationMonoid α]

/-- Prime factors of a polynomial `a` are monic factors of `a` without duplication. -/
def primeFactors (a : α) : Finset α :=
  (normalizedFactors a).toFinset

/-- Radical of a polynomial `a` is a product of prime factors of `a`. -/
def radical (a : α) : α :=
  (primeFactors a).prod id

theorem radical_zero_eq_one : radical (0 : α) = 1 := by
  rw [radical, primeFactors, normalizedFactors_zero, Multiset.toFinset_zero, Finset.prod_empty]

theorem radical_one_eq_one : radical (1 : α) = 1 := by
  rw [radical, primeFactors, normalizedFactors_one, Multiset.toFinset_zero, Finset.prod_empty]

theorem radical_associated_eq {a b : α} (h : Associated a b) : radical a = radical b :=
  by
  rcases iff_iff_and_or_not_and_not.mp h.eq_zero_iff with (⟨rfl, rfl⟩ | ⟨ha, hb⟩)
  · rfl
  · simp_rw [radical, primeFactors]
    rw [(associated_iff_normalizedFactors_eq_normalizedFactors ha hb).mp h]

theorem radical_unit_eq_one {a : α} (h : IsUnit a) : radical a = 1 :=
  (radical_associated_eq (associated_one_iff_isUnit.mpr h)).trans radical_one_eq_one

theorem radical_unit_hMul {u : αˣ} {a : α} : radical ((↑u : α) * a) = radical a :=
  radical_associated_eq (associated_unit_mul_left _ _ u.isUnit)

theorem primeFactors_pow (a : α) {n : ℕ} (hn : 0 < n) : primeFactors (a ^ n) = primeFactors a :=
  by
  simp_rw [primeFactors]
  simp only [normalizedFactors_pow]
  rw [Multiset.toFinset_nsmul]
  exact ne_of_gt hn

theorem radical_pow (a : α) {n : Nat} (hn : 0 < n) : radical (a ^ n) = radical a := by
  simp_rw [radical, primeFactors_pow a hn]

theorem radical_dvd_self (a : α) : radical a ∣ a :=
  by
  by_cases ha : a = 0
  · rw [ha]
    apply dvd_zero
  · rw [radical, ← Finset.prod_val, ← (normalizedFactors_prod ha).dvd_iff_dvd_right]
    apply Multiset.prod_dvd_prod_of_le
    rw [primeFactors, Multiset.toFinset_val]
    apply Multiset.dedup_le

theorem radical_prime {a : α} (ha : Prime a) : radical a = normalize a :=
  by
  rw [radical, primeFactors]
  rw [normalizedFactors_irreducible ha.irreducible]
  simp only [Multiset.toFinset_singleton, id, Finset.prod_singleton]

theorem radical_prime_pow {a : α} (ha : Prime a) {n : ℕ} (hn : 1 ≤ n) :
    radical (a ^ n) = normalize a := by
  rw [radical_pow a hn]
  exact radical_prime ha
