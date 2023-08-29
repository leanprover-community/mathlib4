/-
Copyright (c) 2023 Michael Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Lee
-/
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.MvPolynomial.CommRing
import Mathlib.Data.MvPolynomial.Rename
import Mathlib.Data.Nat.Parity
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Symmetric
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Newton's Identities

This file defines `MvPolynomial` power sums as a means of implementing Newton's identities. The
combinatorial proof, due to Zeilberger, defines for `k : ℕ` a subset `pairs` of
`(range k).powerset × range k` and a map `pairMap` such that `pairMap` is an involution on `pairs`,
and a map `weight` which identifies elements of `pairs` with the terms of the summation in Newton's
identities and which satisfies `weight ∘ pairMap = -weight`. The result therefore follows neatly
from an identity implemented in mathlib as `Finset.sum_involution`. Namely, we use
`Finset.sum_involution` to show that `∑ t in pairs σ k, weight σ R k t = 0`. We then identify
`(-1) ^ k * k * esymm σ R k` with the terms of the weight sum for which `t.fst` has
cardinality `k`, and `(-1) ^ i * esymm σ R i * psum σ R (k - i)` with the terms of the weight sum
for which `t.fst` has cardinality `i` for `i < k` , and we thereby derive the main result
`(-1) ^ k * k * esymm σ R k + ∑ i in range k, (-1) ^ i * esymm σ R i * psum σ R (k - i) = 0` (or
rather, two equivalent forms which provide direct definitions for `esymm` and `psum` in lower-degree
terms).

## Main declarations

* `MvPolynomial.mul_esymm_eq_sum`: a recurrence relation for the `k`th elementary
  symmetric polynomial in terms of lower-degree elementary symmetric polynomials and power sums.

* `MvPolynomial.psum_eq_mul_esymm_sub_sum`: a recurrence relation for the degree-`k` power sum
  in terms of lower-degree elementary symmetric polynomials and power sums.

## References

See [zeilberger1984] for the combinatorial proof of Newton's identities.
-/

open Equiv (Perm)

open BigOperators MvPolynomial

noncomputable section

namespace MvPolynomial

open Finset Nat

variable (σ : Type*) [Fintype σ] [DecidableEq σ] (R : Type*) [CommRing R]

namespace NewtonIdentities

private def pairs (k : ℕ) : Finset (Finset σ × σ) :=
  univ.filter (fun t ↦ card t.fst ≤ k ∧ (card t.fst = k → t.snd ∈ t.fst))

@[simp]
private lemma mem_pairs (k : ℕ) (t : Finset σ × σ) :
    t ∈ pairs σ k ↔ card t.fst ≤ k ∧ (card t.fst = k → t.snd ∈ t.fst) := by
  simp [pairs]
  -- 🎉 no goals

private def weight (k : ℕ) (t : Finset σ × σ) : MvPolynomial σ R :=
  (-1) ^ card t.fst * ((∏ a in t.fst, X a) * X t.snd ^ (k - card t.fst))

private def pairMap (t : Finset σ × σ) : Finset σ × σ :=
  if h : t.snd ∈ t.fst then (t.fst.erase t.snd, t.snd) else (t.fst.cons t.snd h, t.snd)

private lemma pairMap_ne_self (t : Finset σ × σ) : pairMap σ t ≠ t := by
  rw [pairMap]
  -- ⊢ (if h : t.snd ∈ t.fst then (erase t.fst t.snd, t.snd) else (cons t.snd t.fst …
  split_ifs with h1
  -- ⊢ (erase t.fst t.snd, t.snd) ≠ t
  all_goals by_contra ht; rw [← ht] at h1; simp_all
  -- 🎉 no goals

private lemma pairMap_of_snd_mem_fst {t : Finset σ × σ} (h : t.snd ∈ t.fst) :
    pairMap σ t = (t.fst.erase t.snd, t.snd) := by
  simp [pairMap, h]
  -- 🎉 no goals

private lemma pairMap_of_snd_nmem_fst {t : Finset σ × σ} (h : t.snd ∉ t.fst) :
    pairMap σ t = (t.fst.cons t.snd h, t.snd) := by
  simp [pairMap, h]
  -- 🎉 no goals

private theorem pairMap_mem_pairs {k : ℕ} (t : Finset σ × σ) (h : t ∈ pairs σ k) :
    pairMap σ t ∈ pairs σ k := by
  rw [mem_pairs] at h ⊢
  -- ⊢ card (MvPolynomial.NewtonIdentities.pairMap σ t).fst ≤ k ∧ (card (MvPolynomi …
  rcases (em (t.snd ∈ t.fst)) with h1 | h1
  -- ⊢ card (MvPolynomial.NewtonIdentities.pairMap σ t).fst ≤ k ∧ (card (MvPolynomi …
  · rw [pairMap_of_snd_mem_fst σ h1]
    -- ⊢ card (erase t.fst t.snd, t.snd).fst ≤ k ∧ (card (erase t.fst t.snd, t.snd).f …
    simp only [h1, implies_true, and_true] at h
    -- ⊢ card (erase t.fst t.snd, t.snd).fst ≤ k ∧ (card (erase t.fst t.snd, t.snd).f …
    simp only [card_erase_of_mem h1, tsub_le_iff_right, mem_erase, ne_eq, h1]
    -- ⊢ card t.fst ≤ k + 1 ∧ (card t.fst - 1 = k → False)
    refine ⟨le_step h, ?_⟩
    -- ⊢ card t.fst - 1 = k → False
    by_contra h2
    -- ⊢ False
    rw [← h2] at h
    -- ⊢ False
    exact not_le_of_lt (sub_lt (card_pos.mpr ⟨t.snd, h1⟩) zero_lt_one) h
    -- 🎉 no goals
  · rw [pairMap_of_snd_nmem_fst σ h1]
    -- ⊢ card (cons t.snd t.fst h1, t.snd).fst ≤ k ∧ (card (cons t.snd t.fst h1, t.sn …
    simp only [h1] at h
    -- ⊢ card (cons t.snd t.fst h1, t.snd).fst ≤ k ∧ (card (cons t.snd t.fst h1, t.sn …
    simp only [card_cons, mem_cons, true_or, implies_true, and_true]
    -- ⊢ card t.fst + 1 ≤ k
    exact (le_iff_eq_or_lt.mp h.left).resolve_left h.right
    -- 🎉 no goals

@[simp]
private theorem pairMap_involutive : (pairMap σ).Involutive := by
  intro t
  -- ⊢ MvPolynomial.NewtonIdentities.pairMap σ (MvPolynomial.NewtonIdentities.pairM …
  rw [pairMap, pairMap]
  -- ⊢ (if h : (if h : t.snd ∈ t.fst then (erase t.fst t.snd, t.snd) else (cons t.s …
  split_ifs with h1 h2 h3
  · simp at h2
    -- 🎉 no goals
  · simp [insert_erase h1]
    -- 🎉 no goals
  · simp_all
    -- 🎉 no goals
  · simp at h3
    -- 🎉 no goals

private theorem weight_add_weight_pairMap {k : ℕ} (t : Finset σ × σ) (h : t ∈ pairs σ k) :
    weight σ R k t + weight σ R k (pairMap σ t) = 0 := by
  rw [weight, weight]
  -- ⊢ (-1) ^ card t.fst * ((∏ a in t.fst, X a) * X t.snd ^ (k - card t.fst)) + (-1 …
  rw [mem_pairs] at h
  -- ⊢ (-1) ^ card t.fst * ((∏ a in t.fst, X a) * X t.snd ^ (k - card t.fst)) + (-1 …
  have h2 (n : ℕ) : -(-1 : MvPolynomial σ R) ^ n = (-1) ^ (n + 1) := by
    rw [← neg_one_mul ((-1 : MvPolynomial σ R) ^ n), pow_add, pow_one, mul_comm]
  rcases (em (t.snd ∈ t.fst)) with h1 | h1
  -- ⊢ (-1) ^ card t.fst * ((∏ a in t.fst, X a) * X t.snd ^ (k - card t.fst)) + (-1 …
  · rw [pairMap_of_snd_mem_fst σ h1]
    -- ⊢ (-1) ^ card t.fst * ((∏ a in t.fst, X a) * X t.snd ^ (k - card t.fst)) + (-1 …
    simp only [← prod_erase_mul t.fst (fun j ↦ (X j : MvPolynomial σ R)) h1,
      mul_assoc (∏ a in erase t.fst t.snd, X a), card_erase_of_mem h1]
    nth_rewrite 1 [← pow_one (X t.snd)]
    -- ⊢ (-1) ^ card t.fst * ((∏ a in erase t.fst t.snd, X a) * (X t.snd ^ 1 * X t.sn …
    simp only [← pow_add, add_comm]
    -- ⊢ (-1) ^ card t.fst * ((∏ a in erase t.fst t.snd, X a) * X t.snd ^ (k - card t …
    have h3 : 1 ≤ card t.fst := lt_iff_add_one_le.mp (card_pos.mpr ⟨t.snd, h1⟩)
    -- ⊢ (-1) ^ card t.fst * ((∏ a in erase t.fst t.snd, X a) * X t.snd ^ (k - card t …
    rw [← tsub_tsub_assoc h.left h3, ← neg_neg ((-1 : MvPolynomial σ R) ^ (card t.fst - 1)),
      h2 (card t.fst - 1), Nat.sub_add_cancel h3]
    simp
    -- 🎉 no goals
  · rw [pairMap_of_snd_nmem_fst σ h1]
    -- ⊢ (-1) ^ card t.fst * ((∏ a in t.fst, X a) * X t.snd ^ (k - card t.fst)) + (-1 …
    simp only [mul_comm, mul_assoc (∏ a in t.fst, X a), card_cons, prod_cons]
    -- ⊢ (∏ a in t.fst, X a) * (X t.snd ^ (k - card t.fst) * (-1) ^ card t.fst) + (∏  …
    nth_rewrite 2 [← pow_one (X t.snd)]
    -- ⊢ (∏ a in t.fst, X a) * (X t.snd ^ (k - card t.fst) * (-1) ^ card t.fst) + (∏  …
    simp only [← pow_add, ← Nat.add_sub_assoc (Nat.lt_of_le_of_ne h.left (mt h.right h1)), add_comm]
    -- ⊢ (∏ a in t.fst, X a) * (X t.snd ^ (k - card t.fst) * (-1) ^ card t.fst) + (∏  …
    rw [← neg_neg ((-1 : MvPolynomial σ R) ^ card t.fst), h2]
    -- ⊢ (∏ a in t.fst, X a) * (X t.snd ^ (k - card t.fst) * -(-1) ^ (card t.fst + 1) …
    simp
    -- 🎉 no goals

private theorem weight_sum (k : ℕ) : ∑ t in pairs σ k, weight σ R k t = 0 :=
  sum_involution (fun t _ ↦ pairMap σ t) (weight_add_weight_pairMap σ R)
    (fun t _ ↦ (fun _ ↦ pairMap_ne_self σ t)) (pairMap_mem_pairs σ)
    (fun t _ ↦ pairMap_involutive σ t)

private theorem sum_filter_pairs_eq_sum_powersetLen_sum (k : ℕ)
    (f : Finset σ × σ → MvPolynomial σ R) :
    (∑ t in filter (fun t ↦ card t.fst = k) (pairs σ k), f t) =
    ∑ A in powersetLen k univ, (∑ j in A, f (A, j)) := by
  apply sum_finset_product
  -- ⊢ ∀ (p : Finset σ × σ), p ∈ filter (fun t => card t.fst = k) (MvPolynomial.New …
  aesop
  -- 🎉 no goals

private theorem sum_filter_pairs_eq_sum_powersetLen_mem_filter_antidiagonal_sum (k : ℕ) (a : ℕ × ℕ)
    (ha : a ∈ (antidiagonal k).filter (fun a ↦ a.fst < k)) (f : Finset σ × σ → MvPolynomial σ R) :
    (∑ t in filter (fun t ↦ card t.fst = a.fst) (pairs σ k), f t) =
    ∑ A in powersetLen a.fst univ, (∑ j, f (A, j)) := by
  apply sum_finset_product
  -- ⊢ ∀ (p : Finset σ × σ), p ∈ filter (fun t => card t.fst = a.fst) (MvPolynomial …
  simp only [mem_filter, mem_powerset_len_univ_iff, mem_univ, and_true, and_iff_right_iff_imp]
  -- ⊢ ∀ (p : Finset σ × σ), card p.fst = a.fst → p ∈ MvPolynomial.NewtonIdentities …
  rintro p hp
  -- ⊢ p ∈ MvPolynomial.NewtonIdentities.pairs σ k
  have : card p.fst ≤ k := by apply le_of_lt; aesop
  -- ⊢ p ∈ MvPolynomial.NewtonIdentities.pairs σ k
  aesop
  -- 🎉 no goals

private theorem sum_filter_pairs_eq_sum_filter_antidiagonal_powersetLen_sum (k : ℕ)
    (f : Finset σ × σ → MvPolynomial σ R) :
    (∑ t in filter (fun t ↦ card t.fst < k) (pairs σ k), f t) =
    ∑ a in (antidiagonal k).filter (fun a ↦ a.fst < k),
    ∑ A in powersetLen a.fst univ, (∑ j, f (A, j)) := by
  have equiv_i (a : ℕ × ℕ) (ha : a ∈ (antidiagonal k).filter (fun a ↦ a.fst < k)) :=
    sum_filter_pairs_eq_sum_powersetLen_mem_filter_antidiagonal_sum σ R k a ha f
  simp only [← sum_congr rfl equiv_i]
  -- ⊢ ∑ t in filter (fun t => card t.fst < k) (MvPolynomial.NewtonIdentities.pairs …
  have pdisj : Set.PairwiseDisjoint ((antidiagonal k).filter (fun a ↦ a.fst < k))
      (fun (a : ℕ × ℕ) ↦ (filter (fun t ↦ card t.fst = a.fst) (pairs σ k))) := by
    simp only [Set.PairwiseDisjoint, Disjoint, pairs, filter_filter, ne_eq, le_eq_subset,
      bot_eq_empty]
    intro x hx y hy xny s hs hs' a ha
    simp only [mem_univ, forall_true_left, Prod.forall] at hs hs'
    rw [ne_eq, antidiagonal_congr (mem_filter.mp hx).left (mem_filter.mp hy).left,
      ← (mem_filter.mp (hs ha)).right.right, ← (mem_filter.mp (hs' ha)).right.right] at xny
    exact (xny rfl).elim
  have hdisj := @sum_disjiUnion _ _ _ f _ ((antidiagonal k).filter (fun a ↦ a.fst < k))
    (fun (a : ℕ × ℕ) ↦ (filter (fun t ↦ card t.fst = a.fst) (pairs σ k))) pdisj
  have disj_equiv : disjiUnion ((antidiagonal k).filter (fun a ↦ a.fst < k))
      (fun a ↦ filter (fun t ↦ card t.fst = a.fst) (pairs σ k)) pdisj =
      filter (fun t ↦ card t.fst < k) (pairs σ k) := by
    ext a
    rw [mem_disjiUnion, mem_filter]
    refine' ⟨_, fun haf ↦ ⟨(card a.fst, k - card a.fst), _, _⟩⟩
    · rintro ⟨n, hnk, ha⟩
      have hnk' : n.fst ≤ k := by apply le_of_lt; aesop
      aesop
    · simp_all only [mem_antidiagonal, mem_filter, mem_pairs, disjiUnion_eq_biUnion,
        add_tsub_cancel_of_le]
    · simp_all only [mem_antidiagonal, mem_filter, mem_pairs, disjiUnion_eq_biUnion, implies_true]
  simp only [← hdisj, disj_equiv]
  -- 🎉 no goals

private theorem disjoint_filter_pairs_lt_filter_pairs_eq (k : ℕ) :
    Disjoint (filter (fun t ↦ card t.fst < k) (pairs σ k))
    (filter (fun t ↦ card t.fst = k) (pairs σ k)) := by
  rw [disjoint_filter]
  -- ⊢ ∀ (x : Finset σ × σ), x ∈ MvPolynomial.NewtonIdentities.pairs σ k → card x.f …
  exact fun _ _ h1 h2 ↦ lt_irrefl _ (h2.symm.subst h1)
  -- 🎉 no goals

private theorem disjUnion_filter_pairs_eq_pairs (k : ℕ) :
    disjUnion (filter (fun t ↦ card t.fst < k) (pairs σ k))
    (filter (fun t ↦ card t.fst = k) (pairs σ k)) (disjoint_filter_pairs_lt_filter_pairs_eq σ k) =
    pairs σ k := by
  simp only [disjUnion_eq_union, Finset.ext_iff, pairs, filter_filter, mem_filter]
  -- ⊢ ∀ (a : Finset σ × σ), a ∈ filter (fun a => (card a.fst ≤ k ∧ (card a.fst = k …
  intro a
  -- ⊢ a ∈ filter (fun a => (card a.fst ≤ k ∧ (card a.fst = k → a.snd ∈ a.fst)) ∧ c …
  rw [← filter_or, mem_filter]
  -- ⊢ a ∈ univ ∧ ((card a.fst ≤ k ∧ (card a.fst = k → a.snd ∈ a.fst)) ∧ card a.fst …
  refine' ⟨fun ha ↦ by tauto, fun ha ↦ _⟩
  -- ⊢ a ∈ univ ∧ ((card a.fst ≤ k ∧ (card a.fst = k → a.snd ∈ a.fst)) ∧ card a.fst …
  have hacard := le_iff_lt_or_eq.mp ha.2.1
  -- ⊢ a ∈ univ ∧ ((card a.fst ≤ k ∧ (card a.fst = k → a.snd ∈ a.fst)) ∧ card a.fst …
  tauto
  -- 🎉 no goals

private theorem esymm_summand_to_weight (k : ℕ) (A : Finset σ) (h : A ∈ powersetLen k univ) :
    ∑ j in A, weight σ R k (A, j) = k * (-1) ^ k * (∏ i in A, X i : MvPolynomial σ R) := by
  simp [weight, mem_powerset_len_univ_iff.mp h, mul_assoc]
  -- 🎉 no goals

private theorem esymm_to_weight (k : ℕ) : k * esymm σ R k =
    (-1) ^ k * ∑ t in filter (fun t ↦ card t.fst = k) (pairs σ k), weight σ R k t := by
  rw [esymm, sum_filter_pairs_eq_sum_powersetLen_sum σ R k (fun t ↦ weight σ R k t),
    sum_congr rfl (esymm_summand_to_weight σ R k), mul_comm (k : MvPolynomial σ R) ((-1) ^ k),
    ← mul_sum, ← mul_assoc, ← mul_assoc, ← pow_add, Even.neg_one_pow ⟨k, rfl⟩, one_mul]

private theorem esymm_mul_psum_summand_to_weight (k : ℕ) (a : ℕ × ℕ) (ha : a ∈ antidiagonal k) :
    ∑ A in powersetLen a.fst univ, ∑ j, weight σ R k (A, j) =
    (-1) ^ a.fst * esymm σ R a.fst * psum σ R a.snd := by
  simp only [esymm, psum_def, weight, ← mul_assoc, mul_sum]
  -- ⊢ ∑ x in powersetLen a.fst univ, ∑ x_1 : σ, ((-1) ^ card x * ∏ a in x, X a) *  …
  rw [sum_comm]
  -- ⊢ ∑ y : σ, ∑ x in powersetLen a.fst univ, ((-1) ^ card x * ∏ a in x, X a) * X  …
  refine' sum_congr rfl fun x _ ↦ _
  -- ⊢ ∑ x_1 in powersetLen a.fst univ, ((-1) ^ card x_1 * ∏ a in x_1, X a) * X x ^ …
  rw [sum_mul]
  -- ⊢ ∑ x_1 in powersetLen a.fst univ, ((-1) ^ card x_1 * ∏ a in x_1, X a) * X x ^ …
  refine' sum_congr rfl fun s hs ↦ _
  -- ⊢ ((-1) ^ card s * ∏ a in s, X a) * X x ^ (k - card s) = ((-1) ^ a.fst * ∏ a i …
  rw [mem_powerset_len_univ_iff.mp hs, ← mem_antidiagonal.mp ha, add_sub_self_left]
  -- 🎉 no goals

private theorem esymm_mul_psum_to_weight (k : ℕ) :
    ∑ a in (antidiagonal k).filter (fun a ↦ a.fst < k),
    (-1) ^ a.fst * esymm σ R a.fst * psum σ R a.snd =
    ∑ t in filter (fun t ↦ card t.fst < k) (pairs σ k), weight σ R k t := by
  rw [← sum_congr rfl (fun a ha ↦ esymm_mul_psum_summand_to_weight σ R k a (mem_filter.mp ha).left),
    sum_filter_pairs_eq_sum_filter_antidiagonal_powersetLen_sum σ R k]

end NewtonIdentities

/-- **Newton's identities** give a recurrence relation for the kth elementary symmetric polynomial
in terms of lower degree elementary symmetric polynomials and power sums. -/
theorem mul_esymm_eq_sum (k : ℕ) : k * esymm σ R k =
    (-1) ^ (k + 1) * ∑ a in (antidiagonal k).filter (fun a ↦ a.fst < k),
    (-1) ^ a.fst * esymm σ R a.fst * psum σ R a.snd := by
  rw [NewtonIdentities.esymm_to_weight σ R k, NewtonIdentities.esymm_mul_psum_to_weight σ R k,
    eq_comm, ← sub_eq_zero, sub_eq_add_neg, neg_mul_eq_neg_mul,
    neg_eq_neg_one_mul ((-1 : MvPolynomial σ R) ^ k)]
  nth_rw 2 [← pow_one (-1 : MvPolynomial σ R)]
  -- ⊢ (-1) ^ (k + 1) * ∑ t in filter (fun t => card t.fst < k) (MvPolynomial.Newto …
  rw [← pow_add, add_comm 1 k, ← left_distrib,
    ← sum_disjUnion (NewtonIdentities.disjoint_filter_pairs_lt_filter_pairs_eq σ k),
    NewtonIdentities.disjUnion_filter_pairs_eq_pairs σ k, NewtonIdentities.weight_sum σ R k,
    neg_one_pow_mul_eq_zero_iff.mpr rfl]

theorem sum_antidiagonal_card_esymm_psum_eq_zero :
    ∑ a in antidiagonal (Fintype.card σ), (-1) ^ a.fst * esymm σ R a.fst * psum σ R a.snd = 0 := by
  let k := Fintype.card σ
  -- ⊢ ∑ a in antidiagonal (Fintype.card σ), (-1) ^ a.fst * esymm σ R a.fst * psum  …
  suffices : (-1 : MvPolynomial σ R) ^ (k + 1) *
    ∑ a in antidiagonal k, (-1) ^ a.fst * esymm σ R a.fst * psum σ R a.snd = 0
  · simpa using this
    -- 🎉 no goals
  simp [← sum_filter_add_sum_filter_not (antidiagonal k) (fun a ↦ a.fst < k), ← mul_esymm_eq_sum,
    mul_add, ← mul_assoc, ← pow_add, mul_comm ↑k (esymm σ R k)]

/-- A version of Newton's identities which may be more useful in the case that we know the values of
the elementary symmetric polynomials and would like to calculate the values of the power sums. -/
theorem psum_eq_mul_esymm_sub_sum (k : ℕ) (h : 0 < k) : psum σ R k =
    (-1) ^ (k + 1) * k * esymm σ R k -
    ∑ a in (antidiagonal k).filter (fun a ↦ a.fst ∈ Set.Ioo 0 k),
    (-1) ^ a.fst * esymm σ R a.fst * psum σ R a.snd := by
  simp only [Set.Ioo, Set.mem_setOf_eq, and_comm]
  -- ⊢ psum σ R k = (-1) ^ (k + 1) * ↑k * esymm σ R k - ∑ x in filter (fun a => a.f …
  have hesymm := mul_esymm_eq_sum σ R k
  -- ⊢ psum σ R k = (-1) ^ (k + 1) * ↑k * esymm σ R k - ∑ x in filter (fun a => a.f …
  rw [← (sum_filter_add_sum_filter_not ((antidiagonal k).filter (fun a ↦ a.fst < k))
    (fun a ↦ 0 < a.fst) (fun a ↦ (-1) ^ a.fst * esymm σ R a.fst * psum σ R a.snd))] at hesymm
  have sub_both_sides := congrArg (· - (-1 : MvPolynomial σ R) ^ (k + 1) *
    ∑ a in ((antidiagonal k).filter (fun a ↦ a.fst < k)).filter (fun a ↦ 0 < a.fst),
    (-1) ^ a.fst * esymm σ R a.fst * psum σ R a.snd) hesymm
  simp only [left_distrib, add_sub_cancel'] at sub_both_sides
  -- ⊢ psum σ R k = (-1) ^ (k + 1) * ↑k * esymm σ R k - ∑ x in filter (fun a => a.f …
  have sub_both_sides := congrArg ((-1 : MvPolynomial σ R) ^ (k + 1) * ·) sub_both_sides
  -- ⊢ psum σ R k = (-1) ^ (k + 1) * ↑k * esymm σ R k - ∑ x in filter (fun a => a.f …
  simp only [mul_sub_left_distrib, ← mul_assoc, ← pow_add, Even.neg_one_pow ⟨k + 1, rfl⟩, one_mul,
    not_le, lt_one_iff, filter_filter (fun a : ℕ × ℕ ↦ a.fst < k) (fun a ↦ ¬0 < a.fst)]
    at sub_both_sides
  have : filter (fun a ↦ a.fst < k ∧ ¬0 < a.fst) (antidiagonal k) = {(0, k)} := by
    ext a
    rw [mem_filter, mem_antidiagonal, mem_singleton]
    refine' ⟨_, fun ha ↦ by aesop⟩
    rintro ⟨ha, ⟨_, ha0⟩⟩
    rw [← ha, Nat.eq_zero_of_nonpos a.fst ha0, zero_add, ← Nat.eq_zero_of_nonpos a.fst ha0]
  rw [this, sum_singleton] at sub_both_sides
  -- ⊢ psum σ R k = (-1) ^ (k + 1) * ↑k * esymm σ R k - ∑ x in filter (fun a => a.f …
  simp only [_root_.pow_zero, esymm_zero, mul_one, one_mul, filter_filter] at sub_both_sides
  -- ⊢ psum σ R k = (-1) ^ (k + 1) * ↑k * esymm σ R k - ∑ x in filter (fun a => a.f …
  exact sub_both_sides.symm
  -- 🎉 no goals

end MvPolynomial
