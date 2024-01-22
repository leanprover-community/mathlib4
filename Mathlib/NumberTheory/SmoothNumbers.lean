/-
Copyright (c) 2023 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Smooth numbers

We define the set `Nat.smoothNumbers n` consisting of the positive natural numbers all of
whose prime factors are strictly less than `n`.

We also define the finite set `Nat.primesBelow n` to be the set of prime numbers less than `n`.

The main definition `Nat.equivProdNatSmoothNumbers` establishes the bijection between
`ℕ × (smoothNumbers p)` and `smoothNumbers (p+1)` given by sending `(e, n)` to `p^e * n`.
Here `p` is a prime number.
-/

namespace Nat

/-- `primesBelow n` is the set of primes less than `n` as a finset. -/
def primesBelow (n : ℕ) : Finset ℕ := (Finset.range n).filter (fun p ↦ p.Prime)

@[simp]
lemma primesBelow_zero : primesBelow 0 = ∅ := by
  rw [primesBelow, Finset.range_zero, Finset.filter_empty]

lemma prime_of_mem_primesBelow {p n : ℕ} (h : p ∈ n.primesBelow) : p.Prime :=
  (Finset.mem_filter.mp h).2

lemma lt_of_mem_primesBelow {p n : ℕ} (h : p ∈ n.primesBelow) : p < n :=
  Finset.mem_range.mp <| Finset.mem_of_mem_filter p h

lemma primesBelow_succ (n : ℕ) :
    primesBelow n.succ = if n.Prime then insert n (primesBelow n) else primesBelow n := by
  rw [primesBelow, primesBelow, Finset.range_succ, Finset.filter_insert]

lemma not_mem_primesBelow (n : ℕ) : n ∉ primesBelow n :=
  fun hn ↦ (lt_of_mem_primesBelow hn).false

/-- `smoothNumbers n` is the set of *`n`-smooth positive natural numbers*, i.e., the
positive natural numbers all of whose prime factors are less than `n`. -/
def smoothNumbers (n : ℕ) : Set ℕ := {m | m ≠ 0 ∧ ∀ p ∈ factors m, p < n}

lemma mem_smoothNumbers {n m : ℕ} : m ∈ smoothNumbers n ↔ m ≠ 0 ∧ ∀ p ∈ factors m, p < n :=
  Iff.rfl

/-- `m` is `n`-smooth if and only if all prime divisors of `m` are less than `n`. -/
lemma mem_smoothNumbers' {n m : ℕ} : m ∈ smoothNumbers n ↔ ∀ p, p.Prime → p ∣ m → p < n := by
  rw [mem_smoothNumbers]
  refine ⟨fun H p hp h ↦ H.2 p <| (mem_factors_iff_dvd H.1 hp).mpr h,
          fun H ↦ ⟨?_, fun p hp ↦ H p (prime_of_mem_factors hp) (dvd_of_mem_factors hp)⟩⟩
  rintro rfl
  obtain ⟨p, hp₁, hp₂⟩ := exists_infinite_primes n
  exact ((H p hp₂ <| dvd_zero _).trans_le hp₁).false

@[simp]
lemma smoothNumbers_zero : smoothNumbers 0 = {1} := by
  ext m
  rw [Set.mem_singleton_iff, mem_smoothNumbers]
  simp_rw [not_lt_zero]
  rw [← List.eq_nil_iff_forall_not_mem, factors_eq_nil, and_or_left, not_and_self_iff, false_or,
    ne_and_eq_iff_right zero_ne_one]

/-- The product of the prime factors of `n` that are less than `N` is an `N`-smooth number. -/
lemma prod_mem_smoothNumbers (n N : ℕ) : (n.factors.filter (· < N)).prod ∈ smoothNumbers N := by
  have h₀ : (n.factors.filter (· < N)).prod ≠ 0 :=
    List.prod_ne_zero fun h ↦ (pos_of_mem_factors (List.mem_of_mem_filter h)).false
  refine ⟨h₀, fun p hp ↦ ?_⟩
  obtain ⟨H₁, H₂⟩ := (mem_factors h₀).mp hp
  simpa only [decide_eq_true_eq] using List.of_mem_filter <| mem_list_primes_of_dvd_prod H₁.prime
    (fun _ hq ↦ (prime_of_mem_factors (List.mem_of_mem_filter hq)).prime) H₂

/-- The sets of `N`-smooth and of `(N+1)`-smooth numbers are the same when `N` is not prime.
See `Nat.equivProdNatSmoothNumbers` for when `N` is prime. -/
lemma smoothNumbers_succ {N : ℕ} (hN : ¬ N.Prime) : N.succ.smoothNumbers = N.smoothNumbers := by
  ext m
  refine ⟨fun hm ↦ ⟨hm.1, fun p hp ↦ ?_⟩,
         fun hm ↦ ⟨hm.1, fun p hp ↦ (hm.2 p hp).trans <| lt.base N⟩⟩
  exact lt_of_le_of_ne (lt_succ.mp <| hm.2 p hp) fun h ↦ hN <| h ▸ prime_of_mem_factors hp

@[simp] lemma smoothNumbers_one : smoothNumbers 1 = {1} := by
  simp (config := {decide := true}) [smoothNumbers_succ]

@[gcongr] lemma smoothNumbers_mono {N M : ℕ} (hNM : N ≤ M) : N.smoothNumbers ⊆ M.smoothNumbers :=
  fun _ hx ↦ ⟨hx.1, fun p hp => (hx.2 p hp).trans_le hNM⟩

/-- The non-zero non-`N`-smooth numbers are `≥ N`. -/
lemma smoothNumbers_compl (N : ℕ) : (N.smoothNumbers)ᶜ \ {0} ⊆ {n | N ≤ n} := by
  intro n hn
  simp only [Set.mem_compl_iff, mem_smoothNumbers, Set.mem_diff, ne_eq, not_and, not_forall,
    not_lt, exists_prop, Set.mem_singleton_iff] at hn
  obtain ⟨m, hm₁, hm₂⟩ := hn.1 hn.2
  exact hm₂.trans <| le_of_mem_factors hm₁

/-- If `p` is positive and `n` is `p`-smooth, then every product `p^e * n` is `(p+1)`-smooth. -/
lemma pow_mul_mem_smoothNumbers {p n : ℕ} (hp : p ≠ 0) (e : ℕ) (hn : n ∈ smoothNumbers p) :
    p ^ e * n ∈ smoothNumbers (succ p) := by
  have hp' := pow_ne_zero e hp
  refine ⟨mul_ne_zero hp' hn.1, fun q hq ↦ ?_⟩
  rcases (mem_factors_mul hp' hn.1).mp hq with H | H
  · rw [mem_factors hp'] at H
    exact lt_succ.mpr <| le_of_dvd hp.bot_lt <| H.1.dvd_of_dvd_pow H.2
  · exact (hn.2 q H).trans <| lt_succ_self p

/-- If `p` is a prime and `n` is `p`-smooth, then `p` and `n` are coprime. -/
lemma Prime.smoothNumbers_coprime {p n : ℕ} (hp : p.Prime) (hn : n ∈ smoothNumbers p) :
    Nat.Coprime p n := by
  rw [hp.coprime_iff_not_dvd, ← mem_factors_iff_dvd hn.1 hp]
  exact fun H ↦ (hn.2 p H).false

open List Perm in
/-- We establish the bijection from `ℕ × smoothNumbers p` to `smoothNumbers (p+1)`
given by `(e, n) ↦ p^e * n` when `p` is a prime. See `Nat.smoothNumbers_succ` for
when `p` is not prime. -/
def equivProdNatSmoothNumbers {p : ℕ} (hp: p.Prime) :
    ℕ × smoothNumbers p ≃ smoothNumbers p.succ where
  toFun := fun ⟨e, n⟩ ↦ ⟨p ^ e * n, pow_mul_mem_smoothNumbers hp.ne_zero e n.2⟩
  invFun := fun ⟨m, _⟩  ↦ (m.factorization p,
                            ⟨(m.factors.filter (· < p)).prod, prod_mem_smoothNumbers ..⟩)
  left_inv := by
    rintro ⟨e, m, hm₀, hm⟩
    simp (config := { etaStruct := .all }) only
      [Set.coe_setOf, Set.mem_setOf_eq, Prod.mk.injEq, Subtype.mk.injEq]
    constructor
    · rw [factorization_mul (pos_iff_ne_zero.mp <| pos_pow_of_pos e hp.pos) hm₀]
      simp only [factorization_pow, Finsupp.coe_add, Finsupp.coe_smul, nsmul_eq_mul,
        Pi.coe_nat, cast_id, Pi.add_apply, Pi.mul_apply, hp.factorization_self,
        mul_one, add_right_eq_self]
      rw [← factors_count_eq, count_eq_zero]
      exact fun H ↦ (hm p H).false
    · nth_rw 2 [← prod_factors hm₀]
      refine prod_eq <| (filter _ <| perm_factors_mul (pow_ne_zero e hp.ne_zero) hm₀).trans ?_
      rw [filter_append, hp.factors_pow,
          filter_eq_nil.mpr <| fun q hq ↦ by rw [mem_replicate] at hq; simp [hq.2],
          nil_append, filter_eq_self.mpr <| fun q hq ↦ by simp [hm q hq]]
  right_inv := by
    rintro ⟨m, hm₀, hm⟩
    simp only [Set.coe_setOf, Set.mem_setOf_eq, Subtype.mk.injEq]
    rw [← factors_count_eq, ← prod_replicate, ← prod_append]
    nth_rw 3 [← prod_factors hm₀]
    have : m.factors.filter (· = p) = m.factors.filter (¬ · < p)
    · refine (filter_congr' <| fun q hq ↦ ?_).symm
      have H : ¬ p < q := fun hf ↦ Nat.lt_le_asymm hf <| lt_succ_iff.mp (hm q hq)
      simp only [not_lt, le_iff_eq_or_lt, H, or_false, eq_comm, Bool.true_eq_decide_iff]
    refine prod_eq <| (filter_eq' m.factors p).symm ▸ this ▸ perm_append_comm.trans ?_
    convert filter_append_perm ..
    simp only [decide_eq_true_eq]

@[simp]
lemma equivProdNatSmoothNumbers_apply {p e m : ℕ} (hp: p.Prime) (hm : m ∈ p.smoothNumbers) :
    equivProdNatSmoothNumbers hp (e, ⟨m, hm⟩) = p ^ e * m := rfl

@[simp]
lemma equivProdNatSmoothNumbers_apply' {p : ℕ} (hp: p.Prime) (x : ℕ × p.smoothNumbers) :
    equivProdNatSmoothNumbers hp x = p ^ x.1 * x.2 := rfl

end Nat
