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

This file defines `MvPolynomial` power sums as a means of implementing Newton's identities.

## Main declarations

* `MvPolynomial.NewtonIdentities.esymm_recurrence`: a recurrence relation for the kth elementary
  symmetric polynomial in terms of lower degree elementary symmetric polynomials and power sums.

## References

See [zeilberger1984] for the combinatorial proof of Newton's identities.
-/

open Equiv (Perm)

open BigOperators MvPolynomial

noncomputable section

namespace MvPolynomial

namespace NewtonIdentities

open Finset Nat

variable (σ : Type _) [Fintype σ] [DecidableEq σ] (R : Type _) [CommRing R] [NoZeroDivisors R]
  [CharZero R]

private def pairs (k : ℕ) : Finset (Finset σ × σ) :=
  univ.filter (fun t ↦ card t.fst ≤ k ∧ (card t.fst = k → t.snd ∈ t.fst))

@[simp]
private lemma mem_pairs (k : ℕ) (t : Finset σ × σ) :
    t ∈ pairs σ k ↔ card t.fst ≤ k ∧ (card t.fst = k → t.snd ∈ t.fst) := by
  simp [pairs]

private def weight (k : ℕ) (t : Finset σ × σ) : MvPolynomial σ R :=
  (-1) ^ card t.fst * ((∏ a in t.fst, X a) * X t.snd ^ (k - card t.fst))

private def pairMap (t : Finset σ × σ) : Finset σ × σ :=
  if h : t.snd ∈ t.fst then (t.fst.erase t.snd, t.snd) else (t.fst.cons t.snd h, t.snd)

private lemma pairMap_of_snd_mem_fst {t : Finset σ × σ} (h : t.snd ∈ t.fst) :
    pairMap σ t = (t.fst.erase t.snd, t.snd) := by
  simp [pairMap, h]

private lemma pairMap_of_snd_nmem_fst {t : Finset σ × σ} (h : t.snd ∉ t.fst) :
    pairMap σ t = (t.fst.cons t.snd h, t.snd) := by
  simp [pairMap, h]

private theorem pairMap_mem_pairs (t : Finset σ × σ) (h : t ∈ pairs σ k) :
    pairMap σ t ∈ pairs σ k := by
  rw [pairs, mem_filter] at *
  simp only [mem_univ, true_and] at h
  rcases (em (t.snd ∈ t.fst)) with h1 | h1
  · rw [pairMap_of_snd_mem_fst σ h1]
    simp only [h1, implies_true, and_true] at h
    simp only [mem_univ, true_and, card_erase_of_mem h1, tsub_le_iff_right, mem_erase, ne_eq, h1]
    refine ⟨le_step h, ?_⟩
    by_contra h2
    rw [← h2] at h
    exact not_le_of_lt (sub_lt (card_pos.mpr ⟨t.snd, h1⟩) zero_lt_one) h
  · rw [pairMap_of_snd_nmem_fst σ h1]
    simp only [h1] at h
    simp only [mem_univ, true_and, card_cons, mem_cons, true_or, implies_true, and_true]
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

private theorem weight_add_weight_pairMap (t : Finset σ × σ) (h : t ∈ pairs σ k) :
    weight σ R k t + weight σ R k (pairMap σ t) = 0 := by
  rw [weight, weight]
  rw [pairs, mem_filter] at h
  have h2 (n : ℕ) : -(-1 : MvPolynomial σ R) ^ n = (-1) ^ (n + 1) := by
    rw [← neg_one_mul ((-1 : MvPolynomial σ R) ^ n), pow_add, pow_one, mul_comm]
  rcases (em (t.snd ∈ t.fst)) with h1 | h1
  · rw [pairMap_of_snd_mem_fst σ h1]
    simp only [← prod_erase_mul t.fst (fun j ↦ (X j : MvPolynomial σ R)) h1,
      mul_assoc (∏ a in erase t.fst t.snd, X a), card_erase_of_mem h1]
    nth_rewrite 1 [← pow_one (X t.snd)]
    simp only [← pow_add, add_comm]
    have h3 : card t.fst ≥ 1 := lt_iff_add_one_le.mp (card_pos.mpr ⟨t.snd, h1⟩)
    rw [← tsub_tsub_assoc h.right.left h3,
      ← neg_neg ((-1 : MvPolynomial σ R) ^ (card t.fst - 1)), h2 (card t.fst - 1),
      Nat.sub_add_cancel h3]
    simp
  · rw [pairMap_of_snd_nmem_fst σ h1]
    simp only [mul_comm, mul_assoc (∏ a in t.fst, X a), card_cons, prod_cons]
    nth_rewrite 2 [← pow_one (X t.snd)]
    simp only [← pow_add,
      ← Nat.add_sub_assoc (Nat.lt_of_le_of_ne h.right.left (mt h.right.right h1)), add_comm]
    rw [← neg_neg ((-1 : MvPolynomial σ R) ^ card t.fst), h2]
    simp

private theorem weight_eq_zero_of_pairMapEqSelf (t : Finset σ × σ) (h : t ∈ pairs σ k)
    (h2 : pairMap σ t = t) : weight σ R k t = 0 := by
  rw [← eq_neg_self_iff, ← add_eq_zero_iff_eq_neg]
  nth_rw 2 [← h2]
  exact weight_add_weight_pairMap σ R t h

private theorem weight_sum (k : ℕ) : ∑ t in pairs σ k, weight σ R k t = 0 :=
  sum_involution (fun t _ ↦ pairMap σ t) (weight_add_weight_pairMap σ R)
    (fun t h ↦ mt $ weight_eq_zero_of_pairMapEqSelf σ R t h) (pairMap_mem_pairs σ)
    (fun t _ ↦ pairMap_involutive σ t)

private theorem sum_filter_pairs_eq_sum_powersetLen_sum (k : ℕ)
    (f : Finset σ × σ → MvPolynomial σ R) :
    (∑ t in filter (fun t ↦ card t.fst = k) (pairs σ k), f t) =
    ∑ A in powersetLen k univ, (∑ j in A, f (A, j)) := by
  apply sum_finset_product
  simp only [Prod.forall, pairs, mem_filter, mem_univ, true_and]
  intro p b
  refine Iff.intro
    (fun hpl ↦ ⟨mem_powerset_len_univ_iff.mpr hpl.right, hpl.left.right hpl.right⟩) ?_
  intro hpr
  simp only [hpr, implies_true, and_true]
  have cardpk := mem_powerset_len_univ_iff.mp hpr.left
  exact ⟨le_of_eq cardpk, cardpk⟩

private theorem sum_filter_pairs_eq_sum_powersetLen_mem_range_sum (k i : ℕ) (hi : i ∈ range k)
    (f : Finset σ × σ → MvPolynomial σ R) :
    (∑ t in filter (fun t ↦ card t.fst = i) (pairs σ k), f t) =
    ∑ A in powersetLen i univ, (∑ j, f (A, j)) := by
  apply sum_finset_product
  simp only [Prod.forall, pairs, mem_filter, mem_univ, true_and, and_true]
  rw [mem_range] at hi
  intro p b
  refine Iff.intro (fun hpl ↦ mem_powerset_len_univ_iff.mpr hpl.right) ?_
  intro hpr
  refine ⟨?_, mem_powerset_len_univ_iff.mp hpr⟩
  refine ⟨(mem_powerset_len_univ_iff.mp hpr).symm.subst (motive := fun n ↦ n ≤ k)
    (Nat.le_of_lt hi), ?_⟩
  intro cardpk
  rw [← cardpk, mem_powerset_len_univ_iff.mp hpr] at hi
  exact ((lt_irrefl _) hi).elim

private theorem sum_filter_pairs_eq_sum_range_powersetLen_sum (k : ℕ)
    (f : Finset σ × σ → MvPolynomial σ R) :
    (∑ t in filter (fun t ↦ card t.fst < k) (pairs σ k), f t) =
    ∑ i in range k, ∑ A in powersetLen i univ, (∑ j, f (A, j)) := by
  have equiv_i (i : ℕ) (hi : i ∈ range k) :=
    sum_filter_pairs_eq_sum_powersetLen_mem_range_sum σ R k i hi f
  simp only [← sum_congr rfl equiv_i]
  have pdisj : Set.PairwiseDisjoint (range k)
      (fun (i : ℕ) ↦ (filter (fun t ↦ card t.fst = i) (pairs σ k))) := by
    simp only [Set.PairwiseDisjoint, Disjoint, pairs, filter_filter, ne_eq, le_eq_subset,
      bot_eq_empty]
    intro x _ y _ xny s hs hs' a ha
    rw [← (mem_filter.mp (hs ha)).right.right, ← (mem_filter.mp (hs' ha)).right.right] at xny
    exact (xny rfl).elim
  have hdisj := @sum_disjiUnion _ _ _ f _ (range k)
    (fun (i : ℕ) ↦ (filter (fun t ↦ card t.fst = i) (pairs σ k))) pdisj
  have disj_equiv : disjiUnion (range k) (fun i ↦ filter (fun t ↦ card t.fst = i) (pairs σ k))
      pdisj = filter (fun t ↦ card t.fst < k) (pairs σ k) := by
    apply Finset.ext
    intro a
    rw [mem_disjiUnion, mem_filter]
    apply Iff.intro
    · rintro ⟨a1, ha1⟩
      rw [mem_filter] at ha1
      refine ⟨ha1.right.left, ?_⟩
      rw [ha1.right.right]
      exact mem_range.mp ha1.left
    · intro haf
      use card a.fst
      refine ⟨mem_range.mpr haf.right, ?_⟩
      simp_all [mem_filter]
  simp only [← hdisj, disj_equiv]

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
  apply Iff.intro
  · intro ha
    tauto
  · intro ha
    have hacard := le_iff_lt_or_eq.mp ha.right.left
    tauto

private theorem esymm_summand_to_weight (k : ℕ) (A : Finset σ) (h : A ∈ powersetLen k univ) :
    ∑ j in A, weight σ R k (A, j) = k * (-1) ^ k * (∏ i in A, X i : MvPolynomial σ R) := by
  simp [weight, mem_powerset_len_univ_iff.mp h, mul_assoc]

private theorem esymm_to_weight (k : ℕ) : k * esymm σ R k =
    (-1) ^ k * ∑ t in filter (fun t ↦ card t.fst = k) (pairs σ k), weight σ R k t := by
  rw [esymm, sum_filter_pairs_eq_sum_powersetLen_sum σ R k (fun t ↦ weight σ R k t),
    sum_congr rfl (esymm_summand_to_weight σ R k), mul_comm (k : MvPolynomial σ R) ((-1) ^ k),
    ← mul_sum, ← mul_assoc, ← mul_assoc, ← pow_add, Even.neg_one_pow ⟨k, rfl⟩, one_mul]

private theorem esymm_mul_psum_summand_to_weight (k i : ℕ) :
    ∑ A in powersetLen i univ, ∑ j, weight σ R k (A, j) =
    (-1) ^ i * esymm σ R i * psum σ R (k - i) := by
  simp only [esymm, psum_def, weight, ← mul_assoc, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl ?_
  intro x _
  rw [sum_mul]
  refine sum_congr rfl ?_
  intro x1 hx1
  rw [mem_powerset_len_univ_iff.mp hx1]

private theorem esymm_mul_psum_to_weight (k : ℕ) :
    ∑ i in range k, (-1) ^ i * esymm σ R i * psum σ R (k - i) =
    ∑ t in filter (fun t ↦ card t.fst < k) (pairs σ k), weight σ R k t := by
  rw [← sum_congr rfl (fun i _ ↦ esymm_mul_psum_summand_to_weight σ R k i),
    sum_filter_pairs_eq_sum_range_powersetLen_sum σ R k]

/-- **Newton's identities** give a recurrence relation for the kth elementary symmetric polynomial
in terms of lower degree elementary symmetric polynomials and power sums. -/
theorem esymm_recurrence (k : ℕ) : (-1) ^ k * (k * esymm σ R k) +
    ∑ i in range k, (-1) ^ i * esymm σ R i * psum σ R (k - i) = 0 := by
  rw [esymm_to_weight σ R k, esymm_mul_psum_to_weight σ R k, ← mul_assoc, ← pow_add,
    Even.neg_one_pow ⟨k, rfl⟩, one_mul, add_comm,
    ← sum_disjUnion (disjoint_filter_pairs_lt_filter_pairs_eq σ k),
    disjUnion_filter_pairs_eq_pairs σ k, weight_sum σ R k]

/-- A version of Newton's identities which may be more useful in the case that we know the values of
the elementary symmetric polynomials and would like to calculate the values of the power sums. -/
theorem psum_recurrence (k : ℕ) (h : k > 0) : psum σ R k = (-1) ^ (k + 1) * (k * esymm σ R k) -
    ∑ i in Finset.Ico 1 k, (-1) ^ i * esymm σ R i * psum σ R (k - i) := by
  have hesymm := esymm_recurrence σ R k
  have disj : Disjoint {0} (Finset.Ico 1 k) := by simp
  have disju : range k = disjUnion {0} (Finset.Ico 1 k) disj := by
    rw [disjUnion_eq_union]
    apply Finset.ext
    simp only [mem_range, ge_iff_le, mem_union, mem_singleton, mem_Ico]
    intro a
    apply Iff.intro
    · intro ha
      simp only [range, mem_mk, Multiset.mem_range] at ha
      by_contra ha'
      simp only [not_or, not_and, not_lt] at ha'
      rcases ha' with ⟨h1, h2⟩
      exact Nat.not_lt.mpr (h2 (one_le_iff_ne_zero.mpr h1)) ha
    · intro ha
      rcases ha with h1 | h2
      · exact h1.symm.subst h
      · exact h2.right
  rw [disju, sum_disjUnion, sum_singleton] at hesymm
  have sub_both_sides := congrArg (· - (-1) ^ k * (k * esymm σ R k) -
    ∑ i in Finset.Ico 1 k, (-1) ^ i * esymm σ R i * psum σ R (k - i)) hesymm
  simp only [_root_.pow_zero, esymm_zero, one_mul, add_sub_cancel', add_sub_cancel, zero_sub]
    at sub_both_sides
  rw [← neg_mul, ← neg_one_mul] at sub_both_sides
  nth_rw 1 [← pow_one (-1 : MvPolynomial σ R)] at sub_both_sides
  rw [← pow_add, add_comm] at sub_both_sides
  exact sub_both_sides

end NewtonIdentities

end MvPolynomial
