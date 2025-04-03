/-
Copyright (c) 2022 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.Algebra.IsPrimePow
import Mathlib.Data.Nat.Factorization.Basic

#align_import data.nat.factorization.prime_pow from "leanprover-community/mathlib"@"6ca1a09bc9aa75824bf97388c9e3b441fc4ccf3f"

/-!
# Prime powers and factorizations

This file deals with factorizations of prime powers.
-/


variable {R : Type*} [CommMonoidWithZero R] (n p : R) (k : ℕ)

theorem IsPrimePow.minFac_pow_factorization_eq {n : ℕ} (hn : IsPrimePow n) :
    n.minFac ^ n.factorization n.minFac = n := by
  obtain ⟨p, k, hp, hk, rfl⟩ := hn
  rw [← Nat.prime_iff] at hp
  rw [hp.pow_minFac hk.ne', hp.factorization_pow, Finsupp.single_eq_same]
#align is_prime_pow.min_fac_pow_factorization_eq IsPrimePow.minFac_pow_factorization_eq

theorem isPrimePow_of_minFac_pow_factorization_eq {n : ℕ}
    (h : n.minFac ^ n.factorization n.minFac = n) (hn : n ≠ 1) : IsPrimePow n := by
  rcases eq_or_ne n 0 with (rfl | hn')
  · simp_all
  refine ⟨_, _, (Nat.minFac_prime hn).prime, ?_, h⟩
  simp [pos_iff_ne_zero, ← Finsupp.mem_support_iff, Nat.support_factorization, hn',
    Nat.minFac_prime hn, Nat.minFac_dvd]
#align is_prime_pow_of_min_fac_pow_factorization_eq isPrimePow_of_minFac_pow_factorization_eq

theorem isPrimePow_iff_minFac_pow_factorization_eq {n : ℕ} (hn : n ≠ 1) :
    IsPrimePow n ↔ n.minFac ^ n.factorization n.minFac = n :=
  ⟨fun h => h.minFac_pow_factorization_eq, fun h => isPrimePow_of_minFac_pow_factorization_eq h hn⟩
#align is_prime_pow_iff_min_fac_pow_factorization_eq isPrimePow_iff_minFac_pow_factorization_eq

theorem isPrimePow_iff_factorization_eq_single {n : ℕ} :
    IsPrimePow n ↔ ∃ p k : ℕ, 0 < k ∧ n.factorization = Finsupp.single p k := by
  rw [isPrimePow_nat_iff]
  refine exists₂_congr fun p k => ?_
  constructor
  · rintro ⟨hp, hk, hn⟩
    exact ⟨hk, by rw [← hn, Nat.Prime.factorization_pow hp]⟩
  · rintro ⟨hk, hn⟩
    have hn0 : n ≠ 0 := by
      rintro rfl
      simp_all only [Finsupp.single_eq_zero, eq_comm, Nat.factorization_zero, hk.ne']
    rw [Nat.eq_pow_of_factorization_eq_single hn0 hn]
    exact ⟨Nat.prime_of_mem_primeFactors <|
      Finsupp.mem_support_iff.2 (by simp [hn, hk.ne'] : n.factorization p ≠ 0), hk, rfl⟩
#align is_prime_pow_iff_factorization_eq_single isPrimePow_iff_factorization_eq_single

theorem isPrimePow_iff_card_primeFactors_eq_one {n : ℕ} :
    IsPrimePow n ↔ n.primeFactors.card = 1 := by
  simp_rw [isPrimePow_iff_factorization_eq_single, ← Nat.support_factorization,
    Finsupp.card_support_eq_one', pos_iff_ne_zero]
#align is_prime_pow_iff_card_support_factorization_eq_one isPrimePow_iff_card_primeFactors_eq_one

theorem IsPrimePow.exists_ord_compl_eq_one {n : ℕ} (h : IsPrimePow n) :
    ∃ p : ℕ, p.Prime ∧ ord_compl[p] n = 1 := by
  rcases eq_or_ne n 0 with (rfl | hn0); · cases not_isPrimePow_zero h
  rcases isPrimePow_iff_factorization_eq_single.mp h with ⟨p, k, hk0, h1⟩
  rcases em' p.Prime with (pp | pp)
  · refine absurd ?_ hk0.ne'
    simp [← Nat.factorization_eq_zero_of_non_prime n pp, h1]
  refine ⟨p, pp, ?_⟩
  refine Nat.eq_of_factorization_eq (Nat.ord_compl_pos p hn0).ne' (by simp) fun q => ?_
  rw [Nat.factorization_ord_compl n p, h1]
  simp
#align is_prime_pow.exists_ord_compl_eq_one IsPrimePow.exists_ord_compl_eq_one

theorem exists_ord_compl_eq_one_iff_isPrimePow {n : ℕ} (hn : n ≠ 1) :
    IsPrimePow n ↔ ∃ p : ℕ, p.Prime ∧ ord_compl[p] n = 1 := by
  refine ⟨fun h => IsPrimePow.exists_ord_compl_eq_one h, fun h => ?_⟩
  rcases h with ⟨p, pp, h⟩
  rw [isPrimePow_nat_iff]
  rw [← Nat.eq_of_dvd_of_div_eq_one (Nat.ord_proj_dvd n p) h] at hn ⊢
  refine ⟨p, n.factorization p, pp, ?_, by simp⟩
  contrapose! hn
  simp [Nat.le_zero.1 hn]
#align exists_ord_compl_eq_one_iff_is_prime_pow exists_ord_compl_eq_one_iff_isPrimePow

/-- An equivalent definition for prime powers: `n` is a prime power iff there is a unique prime
dividing it. -/
theorem isPrimePow_iff_unique_prime_dvd {n : ℕ} : IsPrimePow n ↔ ∃! p : ℕ, p.Prime ∧ p ∣ n := by
  rw [isPrimePow_nat_iff]
  constructor
  · rintro ⟨p, k, hp, hk, rfl⟩
    refine ⟨p, ⟨hp, dvd_pow_self _ hk.ne'⟩, ?_⟩
    rintro q ⟨hq, hq'⟩
    exact (Nat.prime_dvd_prime_iff_eq hq hp).1 (hq.dvd_of_dvd_pow hq')
  rintro ⟨p, ⟨hp, hn⟩, hq⟩
  rcases eq_or_ne n 0 with (rfl | hn₀)
  · cases (hq 2 ⟨Nat.prime_two, dvd_zero 2⟩).trans (hq 3 ⟨Nat.prime_three, dvd_zero 3⟩).symm
  refine ⟨p, n.factorization p, hp, hp.factorization_pos_of_dvd hn₀ hn, ?_⟩
  simp only [and_imp] at hq
  apply Nat.dvd_antisymm (Nat.ord_proj_dvd _ _)
  -- We need to show n ∣ p ^ n.factorization p
  apply Nat.dvd_of_factors_subperm hn₀
  rw [hp.factors_pow, List.subperm_ext_iff]
  intro q hq'
  rw [Nat.mem_factors hn₀] at hq'
  cases hq _ hq'.1 hq'.2
  simp
#align is_prime_pow_iff_unique_prime_dvd isPrimePow_iff_unique_prime_dvd

theorem isPrimePow_pow_iff {n k : ℕ} (hk : k ≠ 0) : IsPrimePow (n ^ k) ↔ IsPrimePow n := by
  simp only [isPrimePow_iff_unique_prime_dvd]
  apply exists_unique_congr
  simp only [and_congr_right_iff]
  intro p hp
  exact ⟨hp.dvd_of_dvd_pow, fun t => t.trans (dvd_pow_self _ hk)⟩
#align is_prime_pow_pow_iff isPrimePow_pow_iff

theorem Nat.Coprime.isPrimePow_dvd_mul {n a b : ℕ} (hab : Nat.Coprime a b) (hn : IsPrimePow n) :
    n ∣ a * b ↔ n ∣ a ∨ n ∣ b := by
  rcases eq_or_ne a 0 with (rfl | ha)
  · simp only [Nat.coprime_zero_left] at hab
    simp [hab, Finset.filter_singleton, not_isPrimePow_one]
  rcases eq_or_ne b 0 with (rfl | hb)
  · simp only [Nat.coprime_zero_right] at hab
    simp [hab, Finset.filter_singleton, not_isPrimePow_one]
  refine
    ⟨?_, fun h =>
      Or.elim h (fun i => i.trans ((@dvd_mul_right a b a hab).mpr (dvd_refl a)))
          fun i => i.trans ((@dvd_mul_left a b b hab.symm).mpr (dvd_refl b))⟩
  obtain ⟨p, k, hp, _, rfl⟩ := (isPrimePow_nat_iff _).1 hn
  simp only [hp.pow_dvd_iff_le_factorization (mul_ne_zero ha hb), Nat.factorization_mul ha hb,
    hp.pow_dvd_iff_le_factorization ha, hp.pow_dvd_iff_le_factorization hb, Pi.add_apply,
    Finsupp.coe_add]
  have : a.factorization p = 0 ∨ b.factorization p = 0 := by
    rw [← Finsupp.not_mem_support_iff, ← Finsupp.not_mem_support_iff, ← not_and_or, ←
      Finset.mem_inter]
    intro t -- Porting note: used to be `exact` below, but the definition of `∈` has changed.
    simpa using hab.disjoint_primeFactors.le_bot t
  cases' this with h h <;> simp [h, imp_or]
#align nat.coprime.is_prime_pow_dvd_mul Nat.Coprime.isPrimePow_dvd_mul

theorem Nat.mul_divisors_filter_prime_pow {a b : ℕ} (hab : a.Coprime b) :
    (a * b).divisors.filter IsPrimePow = (a.divisors ∪ b.divisors).filter IsPrimePow := by
  rcases eq_or_ne a 0 with (rfl | ha)
  · simp only [Nat.coprime_zero_left] at hab
    simp [hab, Finset.filter_singleton, not_isPrimePow_one]
  rcases eq_or_ne b 0 with (rfl | hb)
  · simp only [Nat.coprime_zero_right] at hab
    simp [hab, Finset.filter_singleton, not_isPrimePow_one]
  ext n
  simp only [ha, hb, Finset.mem_union, Finset.mem_filter, Nat.mul_eq_zero, and_true_iff, Ne,
    and_congr_left_iff, not_false_iff, Nat.mem_divisors, or_self_iff]
  apply hab.isPrimePow_dvd_mul
#align nat.mul_divisors_filter_prime_pow Nat.mul_divisors_filter_prime_pow
