/-
Copyright (c) 2022 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.Algebra.IsPrimePow
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Pow
import Mathlib.NumberTheory.Divisors

/-!
# Prime powers and factorizations

This file deals with factorizations of prime powers.
-/


theorem IsPrimePow.minFac_pow_factorization_eq {n : ℕ} (hn : IsPrimePow n) :
    n.minFac ^ n.factorization n.minFac = n := by
  obtain ⟨p, k, hp, hk, rfl⟩ := hn
  rw [← Nat.prime_iff] at hp
  rw [hp.pow_minFac hk.ne', hp.factorization_pow, Finsupp.single_eq_same]

theorem isPrimePow_of_minFac_pow_factorization_eq {n : ℕ}
    (h : n.minFac ^ n.factorization n.minFac = n) (hn : n ≠ 1) : IsPrimePow n := by
  rcases eq_or_ne n 0 with (rfl | hn')
  · simp_all
  refine ⟨_, _, (Nat.minFac_prime hn).prime, ?_, h⟩
  simp [pos_iff_ne_zero, ← Finsupp.mem_support_iff, Nat.support_factorization, hn',
    Nat.minFac_prime hn, Nat.minFac_dvd]

theorem isPrimePow_iff_minFac_pow_factorization_eq {n : ℕ} (hn : n ≠ 1) :
    IsPrimePow n ↔ n.minFac ^ n.factorization n.minFac = n :=
  ⟨fun h => h.minFac_pow_factorization_eq, fun h => isPrimePow_of_minFac_pow_factorization_eq h hn⟩

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

theorem isPrimePow_iff_card_primeFactors_eq_one {n : ℕ} :
    IsPrimePow n ↔ n.primeFactors.card = 1 := by
  simp_rw [isPrimePow_iff_factorization_eq_single, ← Nat.support_factorization,
    Finsupp.card_support_eq_one', pos_iff_ne_zero]

theorem IsPrimePow.exists_ordCompl_eq_one {n : ℕ} (h : IsPrimePow n) :
    ∃ p : ℕ, p.Prime ∧ ordCompl[p] n = 1 := by
  rcases eq_or_ne n 0 with (rfl | hn0); · cases not_isPrimePow_zero h
  rcases isPrimePow_iff_factorization_eq_single.mp h with ⟨p, k, hk0, h1⟩
  rcases em' p.Prime with (pp | pp)
  · refine absurd ?_ hk0.ne'
    simp [← Nat.factorization_eq_zero_of_non_prime n pp, h1]
  refine ⟨p, pp, ?_⟩
  refine Nat.eq_of_factorization_eq (Nat.ordCompl_pos p hn0).ne' (by simp) fun q => ?_
  rw [Nat.factorization_ordCompl n p, h1]
  simp

theorem exists_ordCompl_eq_one_iff_isPrimePow {n : ℕ} (hn : n ≠ 1) :
    IsPrimePow n ↔ ∃ p : ℕ, p.Prime ∧ ordCompl[p] n = 1 := by
  refine ⟨fun h => IsPrimePow.exists_ordCompl_eq_one h, fun h => ?_⟩
  rcases h with ⟨p, pp, h⟩
  rw [isPrimePow_nat_iff]
  rw [← Nat.eq_of_dvd_of_div_eq_one (Nat.ordProj_dvd n p) h] at hn ⊢
  refine ⟨p, n.factorization p, pp, ?_, by simp⟩
  contrapose! hn
  simp [Nat.le_zero.1 hn]

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
  apply Nat.dvd_antisymm (Nat.ordProj_dvd _ _)
  -- We need to show n ∣ p ^ n.factorization p
  apply Nat.dvd_of_primeFactorsList_subperm hn₀
  rw [hp.primeFactorsList_pow, List.subperm_ext_iff]
  intro q hq'
  rw [Nat.mem_primeFactorsList hn₀] at hq'
  cases hq _ hq'.1 hq'.2
  simp

theorem isPrimePow_pow_iff {n k : ℕ} (hk : k ≠ 0) : IsPrimePow (n ^ k) ↔ IsPrimePow n := by
  simp only [isPrimePow_iff_unique_prime_dvd]
  apply existsUnique_congr
  simp +contextual [Nat.prime_iff, Prime.dvd_pow_iff_dvd, hk]

theorem Nat.Coprime.isPrimePow_dvd_mul {n a b : ℕ} (hab : Nat.Coprime a b) (hn : IsPrimePow n) :
    n ∣ a * b ↔ n ∣ a ∨ n ∣ b := by
  rcases eq_or_ne a 0 with (rfl | ha)
  · simp
  rcases eq_or_ne b 0 with (rfl | hb)
  · simp
  refine
    ⟨?_, fun h =>
      Or.elim h (fun i => i.trans ((@dvd_mul_right a b a hab).mpr (dvd_refl a)))
          fun i => i.trans ((@dvd_mul_left a b b hab.symm).mpr (dvd_refl b))⟩
  obtain ⟨p, k, hp, _, rfl⟩ := (isPrimePow_nat_iff _).1 hn
  simp only [hp.pow_dvd_iff_le_factorization (mul_ne_zero ha hb), Nat.factorization_mul ha hb,
    hp.pow_dvd_iff_le_factorization ha, hp.pow_dvd_iff_le_factorization hb, Pi.add_apply,
    Finsupp.coe_add]
  have : a.factorization p = 0 ∨ b.factorization p = 0 := by
    rw [← Finsupp.notMem_support_iff, ← Finsupp.notMem_support_iff, ← not_and_or, ←
      Finset.mem_inter]
    intro t
    simpa using hab.disjoint_primeFactors.le_bot t
  rcases this with h | h <;> simp [h, imp_or]

theorem Nat.mul_divisors_filter_prime_pow {a b : ℕ} (hab : a.Coprime b) :
    {d ∈ (a * b).divisors | IsPrimePow d} = {d ∈ a.divisors ∪ b.divisors | IsPrimePow d} := by
  rcases eq_or_ne a 0 with (rfl | ha)
  · simp only [Nat.coprime_zero_left] at hab
    simp [hab, Finset.filter_singleton, not_isPrimePow_one]
  rcases eq_or_ne b 0 with (rfl | hb)
  · simp only [Nat.coprime_zero_right] at hab
    simp [hab, Finset.filter_singleton, not_isPrimePow_one]
  ext n
  simp only [ha, hb, Finset.mem_union, Finset.mem_filter, Nat.mul_eq_zero, and_true, Ne,
    and_congr_left_iff, not_false_iff, Nat.mem_divisors, or_self_iff]
  apply hab.isPrimePow_dvd_mul

@[deprecated Nat.factorization_minFac_ne_zero (since := "2025-07-21")]
lemma IsPrimePow.factorization_minFac_ne_zero {n : ℕ} (hn : IsPrimePow n) :
    n.factorization n.minFac ≠ 0 := Nat.factorization_minFac_ne_zero (one_lt hn)

/-- The canonical equivalence between pairs `(p, k)` with `p` a prime and `k : ℕ`
and the set of prime powers given by `(p, k) ↦ p^(k+1)`. -/
def Nat.Primes.prodNatEquiv : Nat.Primes × ℕ ≃ {n : ℕ // IsPrimePow n} where
  toFun pk :=
    ⟨pk.1 ^ (pk.2 + 1), ⟨pk.1, pk.2 + 1, prime_iff.mp pk.1.prop, pk.2.add_one_pos, rfl⟩⟩
  invFun n :=
    (⟨n.val.minFac, minFac_prime n.prop.ne_one⟩, n.val.factorization n.val.minFac - 1)
  left_inv := fun (p, k) ↦ by
    simp only [p.prop.pow_minFac k.add_one_ne_zero, Subtype.coe_eta, factorization_pow, p.prop,
      Prime.factorization, Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.single_add,
      Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same, add_tsub_cancel_right]
  right_inv n := by
    ext1
    dsimp only
    rw [sub_one_add_one (Nat.factorization_minFac_ne_zero n.prop.one_lt),
      n.prop.minFac_pow_factorization_eq]

@[simp]
lemma Nat.Primes.prodNatEquiv_apply (p : Nat.Primes) (k : ℕ) :
    prodNatEquiv (p, k) = ⟨p ^ (k + 1), p, k + 1, prime_iff.mp p.prop, k.add_one_pos, rfl⟩ := rfl

@[simp]
lemma Nat.Primes.coe_prodNatEquiv_apply (p : Nat.Primes) (k : ℕ) :
    (prodNatEquiv (p, k) : ℕ) = p ^ (k + 1) :=
  rfl

@[simp]
lemma Nat.Primes.prodNatEquiv_symm_apply {n : ℕ} (hn : IsPrimePow n) :
    prodNatEquiv.symm ⟨n, hn⟩ =
      (⟨n.minFac, minFac_prime hn.ne_one⟩, n.factorization n.minFac - 1) :=
  rfl
