/-
Copyright (c) 2023 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
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
lemma primesBelow_zero : primesBelow 0 = ∅ := rfl

lemma prime_of_mem_primesBelow {p n : ℕ} (h : p ∈ n.primesBelow) : p.Prime :=
  (Finset.mem_filter.mp h).2

lemma lt_of_mem_primesBelow {p n : ℕ} (h : p ∈ n.primesBelow) : p < n :=
  List.mem_range.mp <| Finset.mem_of_mem_filter p h

lemma primesBelow_succ (n : ℕ) :
    primesBelow n.succ = if n.Prime then insert n (primesBelow n) else primesBelow n := by
  rw [primesBelow, primesBelow, Finset.range_succ, Finset.filter_insert]

lemma not_mem_primesBelow (n : ℕ) : n ∉ primesBelow n := by
  intro hn
  simp [primesBelow] at hn

/-- `smoothNumbers n` is the set of *`n`-smooth positive natural numbers*, i.e., the
positive natural numbers all of whose prime factors are less than `n`. -/
def smoothNumbers (n : ℕ) : Set ℕ := {m | m ≠ 0 ∧ ∀ p ∈ factors m, p < n}

@[simp]
lemma smoothNumbers_zero : smoothNumbers 0 = {1} := by
  have h (m : ℕ) : (∀ p ∈ factors m, p < 0) ↔ m.factors = []
  · rw [List.eq_nil_iff_forall_not_mem]
    exact ⟨fun H p hp ↦ not_succ_le_zero p (H p hp), fun H p hp ↦ False.elim <| H p hp⟩
  ext m
  rw [smoothNumbers, Set.mem_setOf, h, factors_eq_nil,
      (show m ∈ ({1} : Set ℕ) ↔ m = 1 from Set.mem_def), Ne.def]
  exact ⟨fun ⟨H₁, H₂⟩ ↦ H₂.resolve_left H₁, fun H ↦ ⟨H.symm ▸ one_ne_zero, Or.inr H⟩⟩

/-- The product of the prime factors of `n` that are less than `N` is an `N`-smooth number. -/
lemma prod_mem_smoothNumbers (n N : ℕ) : (n.factors.filter (· < N)).prod ∈ smoothNumbers N := by
  have h₀ : (n.factors.filter (· < N)).prod ≠ 0
  · simp only [ne_eq, List.prod_eq_zero_iff]
    intro h
    have H (p : ℕ) (h : p ∈ n.factors) : p ≠ 0 := Prime.ne_zero <| prime_of_mem_factors h
    exact H 0 (List.mem_of_mem_filter h) rfl
  refine ⟨h₀, fun p hp ↦ ?_⟩
  have H := (mem_factors h₀).mp hp
  obtain ⟨q, hq₁, hq₂⟩ := (Prime.dvd_prod_iff <| prime_iff.mp H.1).mp H.2
  have hpq : p = q :=
    (prime_dvd_prime_iff_eq H.1 <| prime_of_mem_factors <| List.mem_of_mem_filter hq₁).mp hq₂
  refine hpq.symm ▸ ?_
  simpa only [decide_eq_true_eq] using List.of_mem_filter hq₁

/-- The sets of `N`-smooth and of `(N+1)`-smooth numbers are the same when `N` is not prime. -/
lemma smoothNumbers_succ {N : ℕ} (hN : ¬ N.Prime) : N.succ.smoothNumbers = N.smoothNumbers := by
  ext m
  refine ⟨fun hm ↦ ⟨hm.1, fun p hp ↦ ?_⟩,
         fun hm ↦ ⟨hm.1, fun p hp ↦ (hm.2 p hp).trans <| lt.base N⟩⟩
  have H : p ≠ N := fun h ↦ hN <| h ▸ prime_of_mem_factors hp
  exact Nat.lt_of_le_of_ne (lt_succ.mp <| hm.2 p hp) H

/-- The non-zero noon-`N`-smooth numbers are `≥ N`. -/
lemma smoothNumbers_compl (N : ℕ) : (N.smoothNumbers)ᶜ \ {0} ⊆ {n | N ≤ n} := by
  intro n hn
  have H := Set.mem_diff_singleton.mp hn
  have H₁ := (Set.mem_compl_iff _ _).mp H.1
  simp only [Nat.smoothNumbers, Set.mem_setOf_eq, not_and, not_forall, not_lt, exists_prop] at H₁
  obtain ⟨m, hm₁, hm₂⟩ := H₁ H.2
  exact hm₂.trans <| le_of_mem_factors hm₁

/-- If `p` is a prime and `n` is `p`-smooth, then every product `p^e * n` is `(p+1)`-smooth. -/
lemma Prime.pow_mul_mem_smoothNumbers {p n : ℕ} (hp : p.Prime) (e : ℕ) (hn : n ∈ smoothNumbers p) :
    p ^ e * n ∈ smoothNumbers (succ p) := by
  have hp' (e : ℕ) : p ^ e ≠ 0 := pow_ne_zero e hp.ne_zero
  refine ⟨mul_ne_zero (hp' e) hn.1, fun q hq ↦ ?_⟩
  rcases (mem_factors_mul (hp' e) hn.1).mp hq with H | H
  · rw [mem_factors <| hp' e] at H
    exact lt_succ.mpr <| le_of_dvd hp.pos <| Prime.dvd_of_dvd_pow H.1 H.2
  · exact (hn.2 q H).trans <| lt.base p

/-- If `p` is a prime and `n` is `p`-smooth, then `p` and `n` are coprime. -/
lemma Prime.smoothNumbers_coprime {p n : ℕ} (hp : p.Prime) (hn : n ∈ smoothNumbers p) :
    Nat.Coprime p n := by
  rw [Prime.coprime_iff_not_dvd hp, ← mem_factors_iff_dvd hn.1 hp]
  exact fun H ↦ lt_irrefl p <| hn.2 p H

open List in
/-- We establish the bijection from `ℕ × smoothNumbers p` to `smoothNumbers (p+1)`
given by `(e, n) ↦ p^e * n` when `p` is a prime. -/
def equivProdNatSmoothNumbers {p : ℕ} (hp: p.Prime) :
    ℕ × smoothNumbers p ≃ smoothNumbers p.succ where
      toFun := fun ⟨e, n⟩ ↦ ⟨p ^ e * n, hp.pow_mul_mem_smoothNumbers e n.2⟩
      invFun := fun ⟨m, _⟩  ↦ (m.factorization p,
                               ⟨(m.factors.filter (· < p)).prod, prod_mem_smoothNumbers ..⟩)
      left_inv := by
        rintro ⟨e, m, hm₀, hm⟩
        simp (config := { etaStruct := .all }) only
          [Set.coe_setOf, Set.mem_setOf_eq, Prod.mk.injEq, Subtype.mk.injEq]
        constructor
        · rw [factorization_mul (pos_iff_ne_zero.mp <| pos_pow_of_pos e hp.pos) hm₀]
          simp only [factorization_pow, Finsupp.coe_add, Finsupp.coe_smul, nsmul_eq_mul,
            Pi.coe_nat, cast_id, Pi.add_apply, Pi.mul_apply, Prime.factorization_self hp,
            mul_one, add_right_eq_self]
          rw [← factors_count_eq, count_eq_zero]
          exact fun H ↦ lt_irrefl p <| hm p H
        · nth_rw 2 [← prod_factors hm₀]
          refine Perm.prod_eq <|
            Perm.trans (Perm.filter _ <| perm_factors_mul (pow_ne_zero e hp.ne_zero) hm₀) ?_
          rw [filter_append, hp.factors_pow,
              filter_eq_nil.mpr <| fun q hq ↦ by rw [mem_replicate] at hq; simp [hq.2],
              nil_append, filter_eq_self.mpr <| fun q hq ↦ by simp [hm q hq]]
      right_inv := by
        rintro ⟨m, hm₀, hm⟩
        simp only [Set.coe_setOf, Set.mem_setOf_eq, Subtype.mk.injEq]
        rw [← factors_count_eq, ← prod_replicate, ← prod_append]
        nth_rw 3 [← prod_factors hm₀]
        refine Perm.prod_eq ?_
        rw [← filter_eq']
        have : m.factors.filter (· = p) = m.factors.filter (¬ · < p)
        · refine (filter_congr' <| fun q hq ↦ ?_).symm
          have H : ¬ p < q := fun hf ↦ Nat.lt_le_asymm hf <| lt_succ_iff.mp (hm q hq)
          simp only [not_lt, le_iff_eq_or_lt, H, or_false, eq_comm, Bool.true_eq_decide_iff]
        rw [this]
        refine perm_append_comm.trans ?_
        convert filter_append_perm ..
        simp

@[simp]
lemma equivProdNatSmoothNumbers_apply {p e m : ℕ} (hp: p.Prime) (hm : m ∈ p.smoothNumbers) :
    equivProdNatSmoothNumbers hp (e, ⟨m, hm⟩) = p ^ e * m := rfl

@[simp]
lemma equivProdNatSmoothNumbers_apply' {p : ℕ} (hp: p.Prime) (x : ℕ × p.smoothNumbers) :
    equivProdNatSmoothNumbers hp x = p ^ x.1 * x.2 := rfl

end Nat
