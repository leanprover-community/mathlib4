/-
Copyright (c) 2023 Michael Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Lee
-/
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.RingTheory.MvPolynomial.Symmetric

/-!
# Newton's Identities

This file defines `MvPolynomial` power sums as a means of implementing Newton's identities. The
combinatorial proof, due to Zeilberger, defines for `k : ℕ` a subset `pairs` of
`(range k).powerset × range k` and a map `pairMap` such that `pairMap` is an involution on `pairs`,
and a map `weight` which identifies elements of `pairs` with the terms of the summation in Newton's
identities and which satisfies `weight ∘ pairMap = -weight`. The result therefore follows neatly
from an identity implemented in mathlib as `Finset.sum_involution`. Namely, we use
`Finset.sum_involution` to show that `∑ t ∈ pairs σ k, weight σ R k t = 0`. We then identify
`(-1) ^ k * k * esymm σ R k` with the terms of the weight sum for which `t.fst` has
cardinality `k`, and `(-1) ^ i * esymm σ R i * psum σ R (k - i)` with the terms of the weight sum
for which `t.fst` has cardinality `i` for `i < k` , and we thereby derive the main result
`(-1) ^ k * k * esymm σ R k + ∑ i ∈ range k, (-1) ^ i * esymm σ R i * psum σ R (k - i) = 0` (or
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

open MvPolynomial

noncomputable section

namespace MvPolynomial

open Finset Nat

namespace NewtonIdentities

variable (σ : Type*) [Fintype σ] [DecidableEq σ] (R : Type*) [CommRing R]

private def pairs (k : ℕ) : Finset (Finset σ × σ) :=
  univ.filter (fun t ↦ card t.fst ≤ k ∧ (card t.fst = k → t.snd ∈ t.fst))

@[simp]
private lemma mem_pairs (k : ℕ) (t : Finset σ × σ) :
    t ∈ pairs σ k ↔ card t.fst ≤ k ∧ (card t.fst = k → t.snd ∈ t.fst) := by
  simp [pairs]

private def weight (k : ℕ) (t : Finset σ × σ) : MvPolynomial σ R :=
  (-1) ^ card t.fst * ((∏ a ∈ t.fst, X a) * X t.snd ^ (k - card t.fst))

private def pairMap (t : Finset σ × σ) : Finset σ × σ :=
  if h : t.snd ∈ t.fst then (t.fst.erase t.snd, t.snd) else (t.fst.cons t.snd h, t.snd)

private lemma pairMap_ne_self (t : Finset σ × σ) : pairMap σ t ≠ t := by
  rw [pairMap]
  split_ifs with h1
  all_goals by_contra ht; rw [← ht] at h1; simp_all

private lemma pairMap_of_snd_mem_fst {t : Finset σ × σ} (h : t.snd ∈ t.fst) :
    pairMap σ t = (t.fst.erase t.snd, t.snd) := by
  simp [pairMap, h]

private lemma pairMap_of_snd_nmem_fst {t : Finset σ × σ} (h : t.snd ∉ t.fst) :
    pairMap σ t = (t.fst.cons t.snd h, t.snd) := by
  simp [pairMap, h]

private theorem pairMap_mem_pairs {k : ℕ} (t : Finset σ × σ) (h : t ∈ pairs σ k) :
    pairMap σ t ∈ pairs σ k := by
  rw [mem_pairs] at h ⊢
  rcases (em (t.snd ∈ t.fst)) with h1 | h1
  · rw [pairMap_of_snd_mem_fst σ h1]
    simp only [h1, implies_true, and_true] at h
    simp only [card_erase_of_mem h1, tsub_le_iff_right, mem_erase, ne_eq, h1]
    refine ⟨le_step h, ?_⟩
    by_contra h2
    simp only [not_true_eq_false, and_true, not_forall, not_false_eq_true, exists_prop] at h2
    rw [← h2] at h
    exact not_le_of_lt (sub_lt (card_pos.mpr ⟨t.snd, h1⟩) zero_lt_one) h
  · rw [pairMap_of_snd_nmem_fst σ h1]
    simp only [h1] at h
    simp only [card_cons, mem_cons, true_or, implies_true, and_true]
    exact (le_iff_eq_or_lt.mp h.left).resolve_left h.right

@[simp]
private theorem pairMap_involutive : (pairMap σ).Involutive := by
  intro t
  rw [pairMap, pairMap]
  split_ifs with h1 h2 h3
  · simp at h2
  · simp [insert_erase h1]
  · simp_all
  · simp at h3

private theorem weight_add_weight_pairMap {k : ℕ} (t : Finset σ × σ) (h : t ∈ pairs σ k) :
    weight σ R k t + weight σ R k (pairMap σ t) = 0 := by
  rw [weight, weight]
  rw [mem_pairs] at h
  have h2 (n : ℕ) : -(-1 : MvPolynomial σ R) ^ n = (-1) ^ (n + 1) := by
    rw [← neg_one_mul ((-1 : MvPolynomial σ R) ^ n), pow_add, pow_one, mul_comm]
  rcases (em (t.snd ∈ t.fst)) with h1 | h1
  · rw [pairMap_of_snd_mem_fst σ h1]
    simp only [← prod_erase_mul t.fst (fun j ↦ (X j : MvPolynomial σ R)) h1,
      mul_assoc (∏ a ∈ erase t.fst t.snd, X a), card_erase_of_mem h1]
    nth_rewrite 1 [← pow_one (X t.snd)]
    simp only [← pow_add, add_comm]
    have h3 : 1 ≤ card t.fst := lt_iff_add_one_le.mp (card_pos.mpr ⟨t.snd, h1⟩)
    rw [← tsub_tsub_assoc h.left h3, ← neg_neg ((-1 : MvPolynomial σ R) ^ (card t.fst - 1)),
      h2 (card t.fst - 1), Nat.sub_add_cancel h3]
    simp
  · rw [pairMap_of_snd_nmem_fst σ h1]
    simp only [mul_comm, mul_assoc (∏ a ∈ t.fst, X a), card_cons, prod_cons]
    nth_rewrite 2 [← pow_one (X t.snd)]
    simp only [← pow_add, ← Nat.add_sub_assoc (Nat.lt_of_le_of_ne h.left (mt h.right h1)), add_comm,
      Nat.succ_eq_add_one, Nat.add_sub_add_right]
    rw [← neg_neg ((-1 : MvPolynomial σ R) ^ card t.fst), h2]
    simp

private theorem weight_sum (k : ℕ) : ∑ t ∈ pairs σ k, weight σ R k t = 0 :=
  sum_involution (fun t _ ↦ pairMap σ t) (weight_add_weight_pairMap σ R)
    (fun t _ ↦ (fun _ ↦ pairMap_ne_self σ t)) (pairMap_mem_pairs σ)
    (fun t _ ↦ pairMap_involutive σ t)

private theorem sum_filter_pairs_eq_sum_powersetCard_sum (k : ℕ)
    (f : Finset σ × σ → MvPolynomial σ R) :
    (∑ t ∈ filter (fun t ↦ card t.fst = k) (pairs σ k), f t) =
    ∑ A ∈ powersetCard k univ, (∑ j ∈ A, f (A, j)) := by
  apply sum_finset_product
  aesop

private theorem sum_filter_pairs_eq_sum_powersetCard_mem_filter_antidiagonal_sum (k : ℕ) (a : ℕ × ℕ)
    (ha : a ∈ (antidiagonal k).filter (fun a ↦ a.fst < k)) (f : Finset σ × σ → MvPolynomial σ R) :
    (∑ t ∈ filter (fun t ↦ card t.fst = a.fst) (pairs σ k), f t) =
    ∑ A ∈ powersetCard a.fst univ, (∑ j, f (A, j)) := by
  apply sum_finset_product
  simp only [mem_filter, mem_powersetCard_univ, mem_univ, and_true, and_iff_right_iff_imp]
  rintro p hp
  have : card p.fst ≤ k := by apply le_of_lt; aesop
  aesop

private lemma filter_pairs_lt (k : ℕ) :
    (pairs σ k).filter (fun (s, _) ↦ s.card < k) =
      (range k).disjiUnion (powersetCard · univ) ((pairwise_disjoint_powersetCard _).set_pairwise _)
        ×ˢ univ := by ext; aesop (add unsafe le_of_lt)

private theorem sum_filter_pairs_eq_sum_filter_antidiagonal_powersetCard_sum (k : ℕ)
    (f : Finset σ × σ → MvPolynomial σ R) :
    ∑ t ∈ (pairs σ k).filter fun t ↦ card t.fst < k, f t =
      ∑ a ∈ (antidiagonal k).filter fun a ↦ a.fst < k,
        ∑ A ∈ powersetCard a.fst univ, ∑ j, f (A, j) := by
  rw [filter_pairs_lt, sum_product, sum_disjiUnion]
  refine sum_nbij' (fun n ↦ (n, k - n)) Prod.fst ?_ ?_ ?_ ?_ ?_ <;>
    simp (config := { contextual := true }) [@eq_comm _ _ k, Nat.add_sub_cancel', le_of_lt]

private theorem disjoint_filter_pairs_lt_filter_pairs_eq (k : ℕ) :
    Disjoint (filter (fun t ↦ card t.fst < k) (pairs σ k))
    (filter (fun t ↦ card t.fst = k) (pairs σ k)) := by
  rw [disjoint_filter]
  exact fun _ _ h1 h2 ↦ lt_irrefl _ (h2.symm.subst h1)

private theorem disjUnion_filter_pairs_eq_pairs (k : ℕ) :
    disjUnion (filter (fun t ↦ card t.fst < k) (pairs σ k))
    (filter (fun t ↦ card t.fst = k) (pairs σ k)) (disjoint_filter_pairs_lt_filter_pairs_eq σ k) =
    pairs σ k := by
  simp only [disjUnion_eq_union, Finset.ext_iff, pairs, filter_filter, mem_filter]
  intro a
  rw [← filter_or, mem_filter]
  refine ⟨fun ha ↦ by tauto, fun ha ↦ ?_⟩
  have hacard := le_iff_lt_or_eq.mp ha.2.1
  tauto

private theorem esymm_summand_to_weight (k : ℕ) (A : Finset σ) (h : A ∈ powersetCard k univ) :
    ∑ j ∈ A, weight σ R k (A, j) = k * (-1) ^ k * (∏ i ∈ A, X i : MvPolynomial σ R) := by
  simp [weight, mem_powersetCard_univ.mp h, mul_assoc]

private theorem esymm_to_weight (k : ℕ) : k * esymm σ R k =
    (-1) ^ k * ∑ t ∈ filter (fun t ↦ card t.fst = k) (pairs σ k), weight σ R k t := by
  rw [esymm, sum_filter_pairs_eq_sum_powersetCard_sum σ R k (fun t ↦ weight σ R k t),
    sum_congr rfl (esymm_summand_to_weight σ R k), mul_comm (k : MvPolynomial σ R) ((-1) ^ k),
    ← mul_sum, ← mul_assoc, ← mul_assoc, ← pow_add, Even.neg_one_pow ⟨k, rfl⟩, one_mul]

private theorem esymm_mul_psum_summand_to_weight (k : ℕ) (a : ℕ × ℕ) (ha : a ∈ antidiagonal k) :
    ∑ A ∈ powersetCard a.fst univ, ∑ j, weight σ R k (A, j) =
    (-1) ^ a.fst * esymm σ R a.fst * psum σ R a.snd := by
  simp only [esymm, psum_def, weight, ← mul_assoc, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun x _ ↦ ?_
  rw [sum_mul]
  refine sum_congr rfl fun s hs ↦ ?_
  rw [mem_powersetCard_univ.mp hs, ← mem_antidiagonal.mp ha, add_sub_self_left]

private theorem esymm_mul_psum_to_weight (k : ℕ) :
    ∑ a ∈ (antidiagonal k).filter (fun a ↦ a.fst < k),
    (-1) ^ a.fst * esymm σ R a.fst * psum σ R a.snd =
    ∑ t ∈ filter (fun t ↦ card t.fst < k) (pairs σ k), weight σ R k t := by
  rw [← sum_congr rfl (fun a ha ↦ esymm_mul_psum_summand_to_weight σ R k a (mem_filter.mp ha).left),
    sum_filter_pairs_eq_sum_filter_antidiagonal_powersetCard_sum σ R k]

end NewtonIdentities

variable (σ : Type*) [Fintype σ] (R : Type*) [CommRing R]

/-- **Newton's identities** give a recurrence relation for the kth elementary symmetric polynomial
in terms of lower degree elementary symmetric polynomials and power sums. -/
theorem mul_esymm_eq_sum (k : ℕ) : k * esymm σ R k =
    (-1) ^ (k + 1) * ∑ a ∈ (antidiagonal k).filter (fun a ↦ a.fst < k),
    (-1) ^ a.fst * esymm σ R a.fst * psum σ R a.snd := by
  classical
  rw [NewtonIdentities.esymm_to_weight σ R k, NewtonIdentities.esymm_mul_psum_to_weight σ R k,
    eq_comm, ← sub_eq_zero, sub_eq_add_neg, neg_mul_eq_neg_mul,
    neg_eq_neg_one_mul ((-1 : MvPolynomial σ R) ^ k)]
  nth_rw 2 [← pow_one (-1 : MvPolynomial σ R)]
  rw [← pow_add, add_comm 1 k, ← left_distrib,
    ← sum_disjUnion (NewtonIdentities.disjoint_filter_pairs_lt_filter_pairs_eq σ k),
    NewtonIdentities.disjUnion_filter_pairs_eq_pairs σ k, NewtonIdentities.weight_sum σ R k,
    neg_one_pow_mul_eq_zero_iff.mpr rfl]

theorem sum_antidiagonal_card_esymm_psum_eq_zero :
    ∑ a ∈ antidiagonal (Fintype.card σ), (-1) ^ a.fst * esymm σ R a.fst * psum σ R a.snd = 0 := by
  let k := Fintype.card σ
  suffices (-1 : MvPolynomial σ R) ^ (k + 1) *
      ∑ a ∈ antidiagonal k, (-1) ^ a.fst * esymm σ R a.fst * psum σ R a.snd = 0 by
    simpa using this
  simp [← sum_filter_add_sum_filter_not (antidiagonal k) (fun a ↦ a.fst < k), ← mul_esymm_eq_sum,
    mul_add, ← mul_assoc, ← pow_add, mul_comm ↑k (esymm σ R k)]

/-- A version of Newton's identities which may be more useful in the case that we know the values of
the elementary symmetric polynomials and would like to calculate the values of the power sums. -/
theorem psum_eq_mul_esymm_sub_sum (k : ℕ) (h : 0 < k) : psum σ R k =
    (-1) ^ (k + 1) * k * esymm σ R k -
    ∑ a ∈ (antidiagonal k).filter (fun a ↦ a.fst ∈ Set.Ioo 0 k),
    (-1) ^ a.fst * esymm σ R a.fst * psum σ R a.snd := by
  simp only [Set.Ioo, Set.mem_setOf_eq, and_comm]
  have hesymm := mul_esymm_eq_sum σ R k
  rw [← (sum_filter_add_sum_filter_not ((antidiagonal k).filter (fun a ↦ a.fst < k))
    (fun a ↦ 0 < a.fst) (fun a ↦ (-1) ^ a.fst * esymm σ R a.fst * psum σ R a.snd))] at hesymm
  have sub_both_sides := congrArg (· - (-1 : MvPolynomial σ R) ^ (k + 1) *
    ∑ a ∈ ((antidiagonal k).filter (fun a ↦ a.fst < k)).filter (fun a ↦ 0 < a.fst),
    (-1) ^ a.fst * esymm σ R a.fst * psum σ R a.snd) hesymm
  simp only [left_distrib, add_sub_cancel_left] at sub_both_sides
  have sub_both_sides := congrArg ((-1 : MvPolynomial σ R) ^ (k + 1) * ·) sub_both_sides
  simp only [mul_sub_left_distrib, ← mul_assoc, ← pow_add, Even.neg_one_pow ⟨k + 1, rfl⟩, one_mul,
    not_le, lt_one_iff, filter_filter (fun a : ℕ × ℕ ↦ a.fst < k) (fun a ↦ ¬0 < a.fst)]
    at sub_both_sides
  have : filter (fun a ↦ a.fst < k ∧ ¬0 < a.fst) (antidiagonal k) = {(0, k)} := by
    ext a
    rw [mem_filter, mem_antidiagonal, mem_singleton]
    refine ⟨?_, by rintro rfl; omega⟩
    rintro ⟨ha, ⟨_, ha0⟩⟩
    rw [← ha, Nat.eq_zero_of_not_pos ha0, zero_add, ← Nat.eq_zero_of_not_pos ha0]
  rw [this, sum_singleton] at sub_both_sides
  simp only [_root_.pow_zero, esymm_zero, mul_one, one_mul, filter_filter] at sub_both_sides
  exact sub_both_sides.symm

end MvPolynomial
