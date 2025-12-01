/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Defs
public import Mathlib.Data.Nat.Factorization.PrimePow
/-!
# Examples of Arithmetic Functions

This file defines some standard examples of arithmetic functions (functions `ℕ → R` vanishing at
`0`, considered as a ring under Dirichlet convolution).

## Main Definitions

* `σ k` is the arithmetic function such that `σ k x = ∑ y ∈ divisors x, y ^ k` for `0 < x`.
* `pow k` is the arithmetic function such that `pow k x = x ^ k` for `0 < x`.
* `id` is the identity arithmetic function on `ℕ`.
* `ω n` is the number of distinct prime factors of `n`.
* `Ω n` is the number of prime factors of `n` counted with multiplicity.
* `μ` is the Möbius function (spelled `moebius` in code).

## Main Results

* Several forms of Möbius inversion:
* `sum_eq_iff_sum_mul_moebius_eq` for functions to a `CommRing`
* `sum_eq_iff_sum_smul_moebius_eq` for functions to an `AddCommGroup`
* `prod_eq_iff_prod_pow_moebius_eq` for functions to a `CommGroup`
* `prod_eq_iff_prod_pow_moebius_eq_of_nonzero` for functions to a `CommGroupWithZero`
* And variants that apply when the equalities only hold on a set `S : Set ℕ` such that
  `m ∣ n → n ∈ S → m ∈ S`:
* `sum_eq_iff_sum_mul_moebius_eq_on` for functions to a `CommRing`
* `sum_eq_iff_sum_smul_moebius_eq_on` for functions to an `AddCommGroup`
* `prod_eq_iff_prod_pow_moebius_eq_on` for functions to a `CommGroup`
* `prod_eq_iff_prod_pow_moebius_eq_on_of_nonzero` for functions to a `CommGroupWithZero`

## Notation

The arithmetic functions `σ`, `ω`, `Ω` and `μ` have Greek letter names.
This notation is scoped to the separate locales `ArithmeticFunction.sigma` for `σ`,
`ArithmeticFunction.omega` for `ω`, `ArithmeticFunction.Omega` for `Ω`, and
`ArithmeticFunction.Moebius` for `μ`, to allow for selective access.

## Tags

arithmetic functions, dirichlet convolution, divisors

-/

@[expose] public section

open Finset Nat

variable {R : Type*}

namespace ArithmeticFunction

section SpecialFunctions

open scoped zeta

/-- The identity on `ℕ` as an `ArithmeticFunction`. -/
def id : ArithmeticFunction ℕ :=
  ⟨_root_.id, rfl⟩

@[simp]
theorem id_apply {x : ℕ} : id x = x :=
  rfl

/-- `pow k n = n ^ k`, except `pow 0 0 = 0`. -/
def pow (k : ℕ) : ArithmeticFunction ℕ :=
  id.ppow k

@[simp]
theorem pow_apply {k n : ℕ} : pow k n = if k = 0 ∧ n = 0 then 0 else n ^ k := by
  cases k <;> simp [pow]

theorem pow_zero_eq_zeta : pow 0 = ζ := by
  ext n
  simp

theorem pow_one_eq_id : pow 1 = id := by
  ext n
  simp

/-- `σ k n` is the sum of the `k`th powers of the divisors of `n` -/
def sigma (k : ℕ) : ArithmeticFunction ℕ :=
  ⟨fun n => ∑ d ∈ divisors n, d ^ k, by simp⟩

@[inherit_doc]
scoped[ArithmeticFunction.sigma] notation "σ" => ArithmeticFunction.sigma

open scoped sigma

theorem sigma_apply {k n : ℕ} : σ k n = ∑ d ∈ divisors n, d ^ k :=
  rfl

@[simp]
theorem sigma_eq_zero {k n : ℕ} : σ k n = 0 ↔ n = 0 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · simp only [ArithmeticFunction.sigma_apply]
    aesop

@[simp]
theorem sigma_pos_iff {k n} : 0 < σ k n ↔ 0 < n := by
  simp [pos_iff_ne_zero]

theorem sigma_apply_prime_pow {k p i : ℕ} (hp : p.Prime) :
    σ k (p ^ i) = ∑ j ∈ .range (i + 1), p ^ (j * k) := by
  simp [sigma_apply, divisors_prime_pow hp, pow_mul]

theorem sigma_one_apply (n : ℕ) : σ 1 n = ∑ d ∈ divisors n, d := by simp [sigma_apply]

theorem sigma_one_apply_prime_pow {p i : ℕ} (hp : p.Prime) :
    σ 1 (p ^ i) = ∑ k ∈ .range (i + 1), p ^ k := by
  simp [sigma_apply_prime_pow hp]

theorem sigma_eq_sum_div (k n : ℕ) : sigma k n = ∑ d ∈ divisors n, (n / d) ^ k := by
  rw [sigma_apply, ← sum_div_divisors]

theorem sigma_zero_apply (n : ℕ) : σ 0 n = #n.divisors := by simp [sigma_apply]

theorem sigma_zero_apply_prime_pow {p i : ℕ} (hp : p.Prime) : σ 0 (p ^ i) = i + 1 := by
  simp [sigma_apply_prime_pow hp]

@[simp]
theorem sigma_one (k : ℕ) : σ k 1 = 1 := by
  simp only [sigma_apply, divisors_one, sum_singleton, one_pow]

theorem sigma_pos (k n : ℕ) (hn0 : n ≠ 0) : 0 < σ k n := by
  rwa [sigma_pos_iff, pos_iff_ne_zero]

theorem sigma_mono (k k' n : ℕ) (hk : k ≤ k') : σ k n ≤ σ k' n := by
  simp_rw [sigma_apply]
  gcongr with d hd
  exact pos_of_mem_divisors hd

theorem zeta_mul_pow_eq_sigma {k : ℕ} : ζ * pow k = σ k := by
  ext
  rw [sigma, zeta_mul_apply]
  apply sum_congr rfl
  aesop

@[arith_mult]
theorem isMultiplicative_one [MonoidWithZero R] : IsMultiplicative (1 : ArithmeticFunction R) :=
  IsMultiplicative.iff_ne_zero.2 ⟨by simp, by
    intro m n hm hn hmn
    by_cases h : m = 1 <;> aesop⟩

@[arith_mult]
theorem isMultiplicative_zeta : IsMultiplicative ζ :=
  IsMultiplicative.iff_ne_zero.2 ⟨by simp, by simp +contextual⟩

@[arith_mult]
theorem isMultiplicative_id : IsMultiplicative ArithmeticFunction.id :=
  ⟨rfl, fun _ => rfl⟩

@[arith_mult]
theorem IsMultiplicative.ppow [CommSemiring R] {f : ArithmeticFunction R} (hf : f.IsMultiplicative)
    {k : ℕ} : IsMultiplicative (f.ppow k) := by
  induction k with
  | zero => exact isMultiplicative_zeta.natCast
  | succ k hi => rw [ppow_succ']; apply hf.pmul hi

@[arith_mult]
theorem isMultiplicative_pow {k : ℕ} : IsMultiplicative (pow k) :=
  isMultiplicative_id.ppow

@[arith_mult]
theorem isMultiplicative_sigma {k : ℕ} : IsMultiplicative (σ k) := by
  rw [← zeta_mul_pow_eq_sigma]
  apply isMultiplicative_zeta.mul isMultiplicative_pow

theorem _root_.Nat.card_divisors {n : ℕ} (hn : n ≠ 0) :
    #n.divisors = n.primeFactors.prod (n.factorization · + 1) := by
  rw [← sigma_zero_apply, isMultiplicative_sigma.multiplicative_factorization _ hn]
  exact prod_congr n.support_factorization fun _ h =>
    sigma_zero_apply_prime_pow <| prime_of_mem_primeFactors h

@[simp]
theorem _root_.Nat.divisors_card_eq_one_iff (n : ℕ) : #n.divisors = 1 ↔ n = 1 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
    exact (card_le_one.mp h.le 1 (one_mem_divisors.mpr hn) n (n.mem_divisors_self hn)).symm

/-- `sigma_eq_one_iff` is to be preferred. -/
private theorem sigma_zero_eq_one_iff (n : ℕ) : σ 0 n = 1 ↔ n = 1 := by
  simp [sigma_zero_apply]

@[simp]
theorem sigma_eq_one_iff (k n : ℕ) : σ k n = 1 ↔ n = 1 := by
  by_cases hn0 : n = 0
  · aesop
  constructor
  · intro h
    rw [← sigma_zero_eq_one_iff]
    have zero_lt_sigma := sigma_pos 0 n hn0
    have sigma_zero_le_sigma := sigma_mono 0 k n k.zero_le
    cutsat
  · simp +contextual

theorem sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul {k n : ℕ} (hn : n ≠ 0) :
    σ k n = ∏ p ∈ n.primeFactors, ∑ i ∈ .range (n.factorization p + 1), p ^ (i * k) := by
  rw [isMultiplicative_sigma.multiplicative_factorization _ hn]
  exact prod_congr n.support_factorization fun _ h ↦
    sigma_apply_prime_pow <| prime_of_mem_primeFactors h

theorem _root_.Nat.sum_divisors {n : ℕ} (hn : n ≠ 0) :
    ∑ d ∈ n.divisors, d = ∏ p ∈ n.primeFactors, ∑ k ∈ .range (n.factorization p + 1), p ^ k := by
  rw [← sigma_one_apply, isMultiplicative_sigma.multiplicative_factorization _ hn]
  exact prod_congr n.support_factorization fun _ h =>
    sigma_one_apply_prime_pow <| prime_of_mem_primeFactors h

/-- `Ω n` is the number of prime factors of `n`. -/
def cardFactors : ArithmeticFunction ℕ :=
  ⟨fun n => n.primeFactorsList.length, by simp⟩

@[inherit_doc]
scoped[ArithmeticFunction.Omega] notation "Ω" => ArithmeticFunction.cardFactors

open scoped Omega

theorem cardFactors_apply {n : ℕ} : Ω n = n.primeFactorsList.length :=
  rfl

lemma cardFactors_zero : Ω 0 = 0 := by simp

@[simp] theorem cardFactors_one : Ω 1 = 0 := by simp [cardFactors_apply]

@[simp]
theorem cardFactors_eq_zero_iff_eq_zero_or_one {n : ℕ} : Ω n = 0 ↔ n = 0 ∨ n = 1 := by
  rw [cardFactors_apply, List.length_eq_zero_iff, primeFactorsList_eq_nil]

@[simp]
theorem cardFactors_pos_iff_one_lt {n : ℕ} : 0 < Ω n ↔ 1 < n := by
  rw [cardFactors_apply, List.length_pos_iff, primeFactorsList_ne_nil]

@[simp]
theorem cardFactors_eq_one_iff_prime {n : ℕ} : Ω n = 1 ↔ n.Prime := by
  refine ⟨fun h => ?_, fun h => List.length_eq_one_iff.2 ⟨n, primeFactorsList_prime h⟩⟩
  cases n with | zero => simp at h | succ n =>
  rcases List.length_eq_one_iff.1 h with ⟨x, hx⟩
  rw [← prod_primeFactorsList n.add_one_ne_zero, hx, List.prod_singleton]
  apply prime_of_mem_primeFactorsList
  rw [hx, List.mem_singleton]

theorem cardFactors_mul {m n : ℕ} (m0 : m ≠ 0) (n0 : n ≠ 0) : Ω (m * n) = Ω m + Ω n := by
  rw [cardFactors_apply, cardFactors_apply, cardFactors_apply, ← Multiset.coe_card, ← factors_eq,
    UniqueFactorizationMonoid.normalizedFactors_mul m0 n0, factors_eq, factors_eq,
    Multiset.card_add, Multiset.coe_card, Multiset.coe_card]

theorem cardFactors_multiset_prod {s : Multiset ℕ} (h0 : s.prod ≠ 0) :
    Ω s.prod = (Multiset.map Ω s).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons ih => simp_all [cardFactors_mul, not_or]

@[simp]
theorem cardFactors_apply_prime {p : ℕ} (hp : p.Prime) : Ω p = 1 :=
  cardFactors_eq_one_iff_prime.2 hp

lemma cardFactors_pow {m k : ℕ} : Ω (m ^ k) = k * Ω m := by
  by_cases hm : m = 0
  · cases k <;> aesop
  induction k with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, cardFactors_mul (pow_ne_zero n hm) hm, ih]
    ring

@[simp]
theorem cardFactors_apply_prime_pow {p k : ℕ} (hp : p.Prime) : Ω (p ^ k) = k := by
  simp [cardFactors_pow, hp]

theorem cardFactors_eq_sum_factorization {n : ℕ} :
    Ω n = n.factorization.sum fun _ k => k := by
  simp [cardFactors_apply, ← List.sum_toFinset_count_eq_length, Finsupp.sum]

/-- `ω n` is the number of distinct prime factors of `n`. -/
def cardDistinctFactors : ArithmeticFunction ℕ :=
  ⟨fun n => n.primeFactorsList.dedup.length, by simp⟩

@[inherit_doc]
scoped[ArithmeticFunction.omega] notation "ω" => ArithmeticFunction.cardDistinctFactors

open scoped omega

theorem cardDistinctFactors_zero : ω 0 = 0 := by simp

@[simp]
theorem cardDistinctFactors_one : ω 1 = 0 := by simp [cardDistinctFactors]

theorem cardDistinctFactors_apply {n : ℕ} : ω n = n.primeFactorsList.dedup.length :=
  rfl

@[simp]
theorem cardDistinctFactors_eq_zero {n : ℕ} : ω n = 0 ↔ n ≤ 1 := by
  simp [cardDistinctFactors_apply, le_one_iff_eq_zero_or_eq_one]

@[simp]
theorem cardDistinctFactors_pos {n : ℕ} : 0 < ω n ↔ 1 < n := by simp [pos_iff_ne_zero]

theorem cardDistinctFactors_eq_cardFactors_iff_squarefree {n : ℕ} (h0 : n ≠ 0) :
    ω n = Ω n ↔ Squarefree n := by
  rw [squarefree_iff_nodup_primeFactorsList h0, cardDistinctFactors_apply]
  constructor <;> intro h
  · rw [← n.primeFactorsList.dedup_sublist.eq_of_length h]
    apply List.nodup_dedup
  · simp [h.dedup, cardFactors]

theorem cardDistinctFactors_eq_one_iff {n : ℕ} : ω n = 1 ↔ IsPrimePow n := by
  rw [ArithmeticFunction.cardDistinctFactors_apply, isPrimePow_iff_card_primeFactors_eq_one,
    ← toFinset_factors, List.card_toFinset]

@[simp]
theorem cardDistinctFactors_apply_prime_pow {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    ω (p ^ k) = 1 :=
  cardDistinctFactors_eq_one_iff.mpr <| hp.isPrimePow.pow hk

@[simp]
theorem cardDistinctFactors_apply_prime {p : ℕ} (hp : p.Prime) : ω p = 1 := by
  rw [← pow_one p, cardDistinctFactors_apply_prime_pow hp one_ne_zero]

theorem cardDistinctFactors_mul {m n : ℕ} (h : m.Coprime n) : ω (m * n) = ω m + ω n := by
  simp [cardDistinctFactors_apply, perm_primeFactorsList_mul_of_coprime h |>.dedup |>.length_eq,
    coprime_primeFactorsList_disjoint h |>.dedup_append]

open scoped Function in
theorem cardDistinctFactors_prod {ι : Type*} {s : Finset ι} {f : ι → ℕ}
    (h : (s : Set ι).Pairwise (Coprime on f)) : ω (∏ i ∈ s, f i) = ∑ i ∈ s, ω (f i) := by
  induction s using cons_induction_on with
  | empty => simp
  | cons a s ha ih =>
    rw [prod_cons, sum_cons, cardDistinctFactors_mul, ih]
    · exact fun x hx y hy hxy => h (by simp [hx]) (by simp [hy]) hxy
    · exact Coprime.prod_right fun i hi =>
        h (by simp) (by simp [hi]) (ne_of_mem_of_not_mem hi ha).symm

/-- `μ` is the Möbius function. If `n` is squarefree with an even number of distinct prime factors,
  `μ n = 1`. If `n` is squarefree with an odd number of distinct prime factors, `μ n = -1`.
  If `n` is not squarefree, `μ n = 0`. -/
def moebius : ArithmeticFunction ℤ :=
  ⟨fun n => if Squarefree n then (-1) ^ cardFactors n else 0, by simp⟩

@[inherit_doc]
scoped[ArithmeticFunction.Moebius] notation "μ" => ArithmeticFunction.moebius

open scoped Moebius

@[simp]
theorem moebius_apply_of_squarefree {n : ℕ} (h : Squarefree n) : μ n = (-1) ^ cardFactors n :=
  if_pos h

@[simp]
theorem moebius_eq_zero_of_not_squarefree {n : ℕ} (h : ¬Squarefree n) : μ n = 0 :=
  if_neg h

theorem moebius_apply_one : μ 1 = 1 := by simp

theorem moebius_ne_zero_iff_squarefree {n : ℕ} : μ n ≠ 0 ↔ Squarefree n := by
  constructor <;> intro h
  · contrapose! h
    simp [h]
  · simp [h]

theorem moebius_eq_or (n : ℕ) : μ n = 0 ∨ μ n = 1 ∨ μ n = -1 := by
  simp only [moebius, coe_mk]
  split_ifs
  · right
    exact neg_one_pow_eq_or ..
  · left
    rfl

theorem moebius_ne_zero_iff_eq_or {n : ℕ} : μ n ≠ 0 ↔ μ n = 1 ∨ μ n = -1 := by
  have := moebius_eq_or n
  cutsat

theorem moebius_sq_eq_one_of_squarefree {l : ℕ} (hl : Squarefree l) : μ l ^ 2 = 1 := by
  rw [moebius_apply_of_squarefree hl, ← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]

theorem abs_moebius_eq_one_of_squarefree {l : ℕ} (hl : Squarefree l) : |μ l| = 1 := by
  simp only [moebius_apply_of_squarefree hl, abs_pow, abs_neg, abs_one, one_pow]

theorem moebius_sq {n : ℕ} :
    μ n ^ 2 = if Squarefree n then 1 else 0 := by
  split_ifs with h
  · exact moebius_sq_eq_one_of_squarefree h
  · simp only [moebius_eq_zero_of_not_squarefree h, zero_pow (show 2 ≠ 0 by simp)]

theorem abs_moebius {n : ℕ} :
    |μ n| = if Squarefree n then 1 else 0 := by
  split_ifs with h
  · exact abs_moebius_eq_one_of_squarefree h
  · simp only [moebius_eq_zero_of_not_squarefree h, abs_zero]

theorem abs_moebius_le_one {n : ℕ} : |μ n| ≤ 1 := by
  rw [abs_moebius, apply_ite (· ≤ 1)]
  simp

theorem moebius_apply_prime {p : ℕ} (hp : p.Prime) : μ p = -1 := by
  rw [moebius_apply_of_squarefree hp.squarefree, cardFactors_apply_prime hp, pow_one]

theorem moebius_apply_prime_pow {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    μ (p ^ k) = if k = 1 then -1 else 0 := by
  split_ifs with h
  · rw [h, pow_one, moebius_apply_prime hp]
  rw [moebius_eq_zero_of_not_squarefree]
  rw [squarefree_pow_iff hp.ne_one hk, not_and_or]
  exact Or.inr h

theorem moebius_apply_isPrimePow_not_prime {n : ℕ} (hn : IsPrimePow n) (hn' : ¬n.Prime) :
    μ n = 0 := by
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).1 hn
  rw [moebius_apply_prime_pow hp hk.ne', if_neg]
  rintro rfl
  exact hn' (by simpa)

@[arith_mult]
theorem isMultiplicative_moebius : IsMultiplicative μ := by
  rw [IsMultiplicative.iff_ne_zero]
  refine ⟨by simp, fun {n m} hn hm hnm => ?_⟩
  simp only [moebius, coe_mk, squarefree_mul hnm, ite_zero_mul_ite_zero, cardFactors_mul hn hm,
    pow_add]

theorem IsMultiplicative.prodPrimeFactors_one_add_of_squarefree [CommSemiring R]
    {f : ArithmeticFunction R} (h_mult : f.IsMultiplicative) {n : ℕ} (hn : Squarefree n) :
    ∏ p ∈ n.primeFactors, (1 + f p) = ∑ d ∈ n.divisors, f d := by
  trans (∏ᵖ p ∣ n, ((ζ : ArithmeticFunction R) + f) p)
  · simp_rw [prodPrimeFactors_apply hn.ne_zero, add_apply, natCoe_apply]
    apply prod_congr rfl; intro p hp
    rw [zeta_apply_ne (prime_of_mem_primeFactorsList <| List.mem_toFinset.mp hp).ne_zero, cast_one]
  rw [isMultiplicative_zeta.natCast.prodPrimeFactors_add_of_squarefree h_mult hn,
    coe_zeta_mul_apply]

theorem IsMultiplicative.prodPrimeFactors_one_sub_of_squarefree [CommRing R]
    (f : ArithmeticFunction R) (hf : f.IsMultiplicative) {n : ℕ} (hn : Squarefree n) :
    ∏ p ∈ n.primeFactors, (1 - f p) = ∑ d ∈ n.divisors, μ d * f d := by
  trans (∏ p ∈ n.primeFactors, (1 + (ArithmeticFunction.pmul (μ : ArithmeticFunction R) f) p))
  · apply prod_congr rfl; intro p hp
    rw [pmul_apply, intCoe_apply, ArithmeticFunction.moebius_apply_prime
        (prime_of_mem_primeFactorsList (List.mem_toFinset.mp hp))]
    ring
  · rw [(isMultiplicative_moebius.intCast.pmul hf).prodPrimeFactors_one_add_of_squarefree hn]
    simp_rw [pmul_apply, intCoe_apply]

open UniqueFactorizationMonoid

@[simp]
theorem moebius_mul_coe_zeta : (μ * ζ : ArithmeticFunction ℤ) = 1 := by
  ext n
  induction n using recOnPosPrimePosCoprime with
  | zero => rw [map_zero, map_zero]
  | one => simp
  | prime_pow p n hp hn =>
    rw [coe_mul_zeta_apply, sum_divisors_prime_pow hp, sum_range_succ']
    simp_rw [pow_zero, moebius_apply_one, moebius_apply_prime_pow hp (succ_ne_zero _), succ_inj,
      sum_ite_eq', mem_range, if_pos hn, neg_add_cancel]
    rw [one_apply_ne]
    rw [Ne, pow_eq_one_iff hn.ne']
    exact hp.ne_one
  | coprime a b _ha _hb hab ha' hb' =>
    rw [IsMultiplicative.map_mul_of_coprime _ hab, ha', hb',
      IsMultiplicative.map_mul_of_coprime isMultiplicative_one hab]
    exact isMultiplicative_moebius.mul isMultiplicative_zeta.natCast

@[simp]
theorem coe_zeta_mul_moebius : (ζ * μ : ArithmeticFunction ℤ) = 1 := by
  rw [mul_comm, moebius_mul_coe_zeta]

@[simp]
theorem coe_moebius_mul_coe_zeta [Ring R] : (μ * ζ : ArithmeticFunction R) = 1 := by
  rw [← coe_coe, ← intCoe_mul, moebius_mul_coe_zeta, intCoe_one]

@[simp]
theorem coe_zeta_mul_coe_moebius [Ring R] : (ζ * μ : ArithmeticFunction R) = 1 := by
  rw [← coe_coe, ← intCoe_mul, coe_zeta_mul_moebius, intCoe_one]

section CommRing

variable [CommRing R]

instance : Invertible (ζ : ArithmeticFunction R) where
  invOf := μ
  invOf_mul_self := coe_moebius_mul_coe_zeta
  mul_invOf_self := coe_zeta_mul_coe_moebius

/-- A unit in `ArithmeticFunction R` that evaluates to `ζ`, with inverse `μ`. -/
def zetaUnit : (ArithmeticFunction R)ˣ :=
  ⟨ζ, μ, coe_zeta_mul_coe_moebius, coe_moebius_mul_coe_zeta⟩

@[simp]
theorem coe_zetaUnit : ((zetaUnit : (ArithmeticFunction R)ˣ) : ArithmeticFunction R) = ζ :=
  rfl

@[simp]
theorem inv_zetaUnit : ((zetaUnit⁻¹ : (ArithmeticFunction R)ˣ) : ArithmeticFunction R) = μ :=
  rfl

end CommRing

/-- Möbius inversion for functions to an `AddCommGroup`. -/
theorem sum_eq_iff_sum_smul_moebius_eq [AddCommGroup R] {f g : ℕ → R} :
    (∀ n > 0, ∑ i ∈ n.divisors, f i = g n) ↔
      ∀ n > 0, ∑ x ∈ n.divisorsAntidiagonal, μ x.fst • g x.snd = f n := by
  let f' : ArithmeticFunction R := ⟨fun x => if x = 0 then 0 else f x, if_pos rfl⟩
  let g' : ArithmeticFunction R := ⟨fun x => if x = 0 then 0 else g x, if_pos rfl⟩
  trans (ζ : ArithmeticFunction ℤ) • f' = g'
  · rw [ArithmeticFunction.ext_iff]
    apply forall_congr'
    intro n
    cases n with
    | zero => simp
    | succ n =>
      rw [coe_zeta_smul_apply]
      simp only [forall_prop_of_true, succ_pos', f', g', coe_mk, succ_ne_zero, ite_false]
      rw [sum_congr rfl fun x hx => if_neg (pos_of_mem_divisors hx).ne']
  trans μ • g' = f'
  · constructor <;> intro h <;>
      simp only [← h, ← mul_smul, moebius_mul_coe_zeta, coe_zeta_mul_moebius, one_smul]
  · rw [ArithmeticFunction.ext_iff]
    apply forall_congr'
    intro n
    cases n with
    | zero => simp
    | succ n =>
      simp only [forall_prop_of_true, succ_pos', smul_apply, f', g', coe_mk, succ_ne_zero,
        ite_false]
      rw [sum_congr rfl fun x hx => ?_]
      rw [if_neg (pos_of_mem_divisors (snd_mem_divisors_of_mem_antidiagonal hx)).ne']

/-- Möbius inversion for functions to a `Ring`. -/
theorem sum_eq_iff_sum_mul_moebius_eq [NonAssocRing R] {f g : ℕ → R} :
    (∀ n > 0, ∑ i ∈ n.divisors, f i = g n) ↔
      ∀ n > 0, ∑ x ∈ n.divisorsAntidiagonal, (μ x.fst : R) * g x.snd = f n := by
  rw [sum_eq_iff_sum_smul_moebius_eq]
  apply forall_congr'
  refine fun a => imp_congr_right fun _ => (sum_congr rfl fun x _hx => ?_).congr_left
  rw [zsmul_eq_mul]

/-- Möbius inversion for functions to a `CommGroup`. -/
theorem prod_eq_iff_prod_pow_moebius_eq [CommGroup R] {f g : ℕ → R} :
    (∀ n > 0, ∏ i ∈ n.divisors, f i = g n) ↔
      ∀ n > 0, ∏ x ∈ n.divisorsAntidiagonal, g x.snd ^ μ x.fst = f n :=
  @sum_eq_iff_sum_smul_moebius_eq (Additive R) _ _ _

/-- Möbius inversion for functions to a `CommGroupWithZero`. -/
theorem prod_eq_iff_prod_pow_moebius_eq_of_nonzero [CommGroupWithZero R] {f g : ℕ → R}
    (hf : ∀ n : ℕ, 0 < n → f n ≠ 0) (hg : ∀ n : ℕ, 0 < n → g n ≠ 0) :
    (∀ n > 0, ∏ i ∈ n.divisors, f i = g n) ↔
      ∀ n > 0, ∏ x ∈ n.divisorsAntidiagonal, g x.snd ^ μ x.fst = f n := by
  refine
      Iff.trans
        (Iff.trans (forall_congr' fun n => ?_)
          (@prod_eq_iff_prod_pow_moebius_eq Rˣ _
            (fun n => if h : 0 < n then Units.mk0 (f n) (hf n h) else 1) fun n =>
            if h : 0 < n then Units.mk0 (g n) (hg n h) else 1))
        (forall_congr' fun n => ?_) <;>
    refine imp_congr_right fun hn => ?_
  · dsimp
    rw [dif_pos hn, ← Units.val_inj, ← Units.coeHom_apply, map_prod, Units.val_mk0,
      prod_congr rfl _]
    intro x hx
    rw [dif_pos (pos_of_mem_divisors hx), Units.coeHom_apply, Units.val_mk0]
  · dsimp
    rw [dif_pos hn, ← Units.val_inj, ← Units.coeHom_apply, map_prod, Units.val_mk0,
      prod_congr rfl _]
    intro x hx
    rw [dif_pos (pos_of_mem_divisors (snd_mem_divisors_of_mem_antidiagonal hx)), Units.coeHom_apply,
      Units.val_zpow_eq_zpow_val, Units.val_mk0]

/-- Möbius inversion for functions to an `AddCommGroup`, where the equalities only hold on a
well-behaved set. -/
theorem sum_eq_iff_sum_smul_moebius_eq_on [AddCommGroup R] {f g : ℕ → R}
    (s : Set ℕ) (hs : ∀ m n, m ∣ n → n ∈ s → m ∈ s) :
    (∀ n > 0, n ∈ s → (∑ i ∈ n.divisors, f i) = g n) ↔
      ∀ n > 0, n ∈ s → (∑ x ∈ n.divisorsAntidiagonal, μ x.fst • g x.snd) = f n := by
  constructor
  · intro h
    let G := fun (n : ℕ) => (∑ i ∈ n.divisors, f i)
    intro n hn hnP
    suffices ∑ d ∈ n.divisors, μ (n/d) • G d = f n by
      rw [sum_divisorsAntidiagonal' (f := fun x y => μ x • g y), ← this, sum_congr rfl]
      intro d hd
      rw [← h d (pos_of_mem_divisors hd) <| hs d n (dvd_of_mem_divisors hd) hnP]
    rw [← sum_divisorsAntidiagonal' (f := fun x y => μ x • G y)]
    apply sum_eq_iff_sum_smul_moebius_eq.mp _ n hn
    intro _ _; rfl
  · intro h
    let F := fun (n : ℕ) => ∑ x ∈ n.divisorsAntidiagonal, μ x.fst • g x.snd
    intro n hn hnP
    suffices ∑ d ∈ n.divisors, F d = g n by
      rw [← this, sum_congr rfl]
      intro d hd
      rw [← h d (pos_of_mem_divisors hd) <| hs d n (dvd_of_mem_divisors hd) hnP]
    apply sum_eq_iff_sum_smul_moebius_eq.mpr _ n hn
    intro _ _; rfl

theorem sum_eq_iff_sum_smul_moebius_eq_on' [AddCommGroup R] {f g : ℕ → R}
    (s : Set ℕ) (hs : ∀ m n, m ∣ n → n ∈ s → m ∈ s) (hs₀ : 0 ∉ s) :
    (∀ n ∈ s, (∑ i ∈ n.divisors, f i) = g n) ↔
     ∀ n ∈ s, (∑ x ∈ n.divisorsAntidiagonal, μ x.fst • g x.snd) = f n := by
  have : ∀ P : ℕ → Prop, ((∀ n ∈ s, P n) ↔ (∀ n > 0, n ∈ s → P n)) := fun P ↦ by
    refine forall_congr' (fun n ↦ ⟨fun h _ ↦ h, fun h hn ↦ h ?_ hn⟩)
    contrapose! hs₀
    simpa [nonpos_iff_eq_zero.mp hs₀] using hn
  simpa only [this] using sum_eq_iff_sum_smul_moebius_eq_on s hs

/-- Möbius inversion for functions to a `Ring`, where the equalities only hold on a well-behaved
set. -/
theorem sum_eq_iff_sum_mul_moebius_eq_on [NonAssocRing R] {f g : ℕ → R}
    (s : Set ℕ) (hs : ∀ m n, m ∣ n → n ∈ s → m ∈ s) :
    (∀ n > 0, n ∈ s → (∑ i ∈ n.divisors, f i) = g n) ↔
      ∀ n > 0, n ∈ s →
        (∑ x ∈ n.divisorsAntidiagonal, (μ x.fst : R) * g x.snd) = f n := by
  rw [sum_eq_iff_sum_smul_moebius_eq_on s hs]
  apply forall_congr'
  intro a; refine imp_congr_right ?_
  refine fun _ => imp_congr_right fun _ => (sum_congr rfl fun x _hx => ?_).congr_left
  rw [zsmul_eq_mul]

/-- Möbius inversion for functions to a `CommGroup`, where the equalities only hold on a
well-behaved set. -/
theorem prod_eq_iff_prod_pow_moebius_eq_on [CommGroup R] {f g : ℕ → R}
    (s : Set ℕ) (hs : ∀ m n, m ∣ n → n ∈ s → m ∈ s) :
    (∀ n > 0, n ∈ s → (∏ i ∈ n.divisors, f i) = g n) ↔
      ∀ n > 0, n ∈ s → (∏ x ∈ n.divisorsAntidiagonal, g x.snd ^ μ x.fst) = f n :=
  @sum_eq_iff_sum_smul_moebius_eq_on (Additive R) _ _ _ s hs

/-- Möbius inversion for functions to a `CommGroupWithZero`, where the equalities only hold on
a well-behaved set. -/
theorem prod_eq_iff_prod_pow_moebius_eq_on_of_nonzero [CommGroupWithZero R]
    (s : Set ℕ) (hs : ∀ m n, m ∣ n → n ∈ s → m ∈ s) {f g : ℕ → R}
    (hf : ∀ n > 0, f n ≠ 0) (hg : ∀ n > 0, g n ≠ 0) :
    (∀ n > 0, n ∈ s → (∏ i ∈ n.divisors, f i) = g n) ↔
      ∀ n > 0, n ∈ s → (∏ x ∈ n.divisorsAntidiagonal, g x.snd ^ μ x.fst) = f n := by
  refine
      Iff.trans
        (Iff.trans (forall_congr' fun n => ?_)
          (@prod_eq_iff_prod_pow_moebius_eq_on Rˣ _
            (fun n => if h : 0 < n then Units.mk0 (f n) (hf n h) else 1)
            (fun n => if h : 0 < n then Units.mk0 (g n) (hg n h) else 1)
            s hs) )
        (forall_congr' fun n => ?_) <;>
    refine imp_congr_right fun hn => ?_
  · dsimp
    rw [dif_pos hn, ← Units.val_inj, ← Units.coeHom_apply, map_prod, Units.val_mk0,
      prod_congr rfl _]
    intro x hx
    rw [dif_pos (pos_of_mem_divisors hx), Units.coeHom_apply, Units.val_mk0]
  · dsimp
    rw [dif_pos hn, ← Units.val_inj, ← Units.coeHom_apply, map_prod, Units.val_mk0,
      prod_congr rfl _]
    intro x hx
    rw [dif_pos (pos_of_mem_divisors (snd_mem_divisors_of_mem_antidiagonal hx)),
      Units.coeHom_apply, Units.val_zpow_eq_zpow_val, Units.val_mk0]

end SpecialFunctions

section Sum

theorem sum_Ioc_zeta (N : ℕ) : ∑ n ∈ Ioc 0 N, zeta n = N := by
  simp only [zeta_apply, sum_ite, sum_const_zero, sum_const, smul_eq_mul, mul_one, zero_add]
  rw [show {x ∈ Ioc 0 N | ¬x = 0} = Ioc 0 N by ext; simp; cutsat]
  simp

variable {R : Type*} [Semiring R]

theorem sum_Ioc_mul_eq_sum_prod_filter (f g : ArithmeticFunction R) (N : ℕ) :
    ∑ n ∈ Ioc 0 N, (f * g) n = ∑ x ∈ Ioc 0 N ×ˢ Ioc 0 N with x.1 * x.2 ≤ N, f x.1 * g x.2 := by
  simp only [mul_apply]
  trans ∑ n ∈ Ioc 0 N, ∑ x ∈ Ioc 0 N ×ˢ Ioc 0 N with x.1 * x.2 = n, f x.1 * g x.2
  · refine sum_congr rfl fun n hn ↦ ?_
    simp only [mem_Ioc] at hn
    have hn0 : n ≠ 0 := by exact ne_zero_of_lt hn.1
    rw [divisorsAntidiagonal_eq_prod_filter_of_le hn0 hn.2]
  · simp_rw [sum_filter]
    rw [sum_comm]
    exact sum_congr rfl fun _ _ ↦ (by simp_all)

theorem sum_Ioc_mul_eq_sum_sum (f g : ArithmeticFunction R) (N : ℕ) :
    ∑ n ∈ Ioc 0 N, (f * g) n = ∑ n ∈ Ioc 0 N, f n * ∑ m ∈ Ioc 0 (N / n), g m := by
  rw [sum_Ioc_mul_eq_sum_prod_filter, sum_filter, sum_product]
  refine sum_congr rfl fun n hn ↦ ?_
  simp only [sum_ite, not_le, sum_const_zero, add_zero, mul_sum]
  congr
  ext
  simp only [mem_filter, mem_Ioc, and_assoc, and_congr_right_iff] at hn ⊢
  intro _
  constructor
  · intro ⟨_, h⟩
    grw [← h, Nat.mul_div_cancel_left _ (by omega)]
  · intro hm
    grw [hm]
    simp [mul_div_le, div_le_self]

theorem sum_Ioc_mul_zeta_eq_sum (f : ArithmeticFunction R) (N : ℕ) :
    ∑ n ∈ Ioc 0 N, (f * zeta) n = ∑ n ∈ Ioc 0 N, f n * ↑(N / n) := by
  rw [sum_Ioc_mul_eq_sum_sum]
  refine sum_congr rfl fun n hn ↦ ?_
  simp_rw [natCoe_apply]
  rw_mod_cast [sum_Ioc_zeta]

--TODO: Dirichlet hyperbola method to get sums of length `sqrt N`
/-- An `O(N)` formula for the sum of the number of divisors function. -/
theorem sum_Ioc_sigma0_eq_sum_div (N : ℕ) :
    ∑ n ∈ Ioc 0 N, sigma 0 n = ∑ n ∈ Ioc 0 N, (N / n) := by
  rw [← zeta_mul_pow_eq_sigma, pow_zero_eq_zeta]
  convert sum_Ioc_mul_zeta_eq_sum zeta N using 1
  simpa using sum_congr rfl (by grind)

end Sum
end ArithmeticFunction

namespace Nat.Coprime

open ArithmeticFunction

theorem card_divisors_mul {m n : ℕ} (hmn : m.Coprime n) :
    #(m * n).divisors = #m.divisors * #n.divisors := by
  simp only [← sigma_zero_apply, isMultiplicative_sigma.map_mul_of_coprime hmn]

theorem sum_divisors_mul {m n : ℕ} (hmn : m.Coprime n) :
    ∑ d ∈ (m * n).divisors, d = (∑ d ∈ m.divisors, d) * ∑ d ∈ n.divisors, d := by
  simp only [← sigma_one_apply, isMultiplicative_sigma.map_mul_of_coprime hmn]

end Nat.Coprime

namespace Mathlib.Meta.Positivity
open Lean Meta Qq

/-- Extension for `ArithmeticFunction.sigma`. -/
@[positivity ArithmeticFunction.sigma _ _]
meta def evalArithmeticFunctionSigma : PositivityExt where eval {u α} z p e := do
  match u, α, e with
  | 0, ~q(ℕ), ~q(ArithmeticFunction.sigma $k $n) =>
    let rn ← core z p n
    assumeInstancesCommute
    match rn with
    | .positive pn => return .positive q(Iff.mpr ArithmeticFunction.sigma_pos_iff $pn)
    | _ => return .nonnegative q(Nat.zero_le _)
  | _, _, _ => throwError "not ArithmeticFunction.sigma"


end Mathlib.Meta.Positivity
