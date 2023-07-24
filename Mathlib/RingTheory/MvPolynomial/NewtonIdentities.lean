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
import Mathlib.RingTheory.MvPolynomial.Symmetric

/-!
# Newton's Identities

This file defines `MvPolynomial` power sums as a means of implementing Newton's identities.

## Main declarations

* `MvPolynomial.psum`

* `MvPolynomial.esymm_recurrence` encapsulating the primary result

## Notation

+ `psum σ R n` is the degree-`n` power sum in `MvPolynomial σ R`.

As in other polynomial files, we typically use the notation:

+ `σ τ : Type _` (indexing the variables)

+ `R S : Type _` `[CommSemiring R]` `[CommSemiring S]` (the coefficients)

+ `r : R` elements of the coefficient ring

+ `i : σ`, with corresponding monomial `X i`, often denoted `X_i` by mathematicians

+ `φ ψ : MvPolynomial σ R`

## References

See [zeilberger1984] for the combinatorial proof of Newton's identities.
-/

open Equiv (Perm)

open BigOperators MvPolynomial

noncomputable section

section PowerSum

namespace Multiset

variable {R : Type _} [CommSemiring R]

/-- The degree-`n` power sum evaluated at the elements of `s` -/
def psum (s : Multiset R) (n : ℕ) : R := (s.map (fun (x : R) ↦ x ^ n)).sum

end Multiset

open Finset

variable (σ R) [CommSemiring R] [Fintype σ] [Fintype τ]

/-- The degree-`n` power sum -/
def psum (n : ℕ) : MvPolynomial σ R := ∑ i, (X i) ^ n

theorem rename_psum (n : ℕ) (e : σ ≃ τ) : rename e (psum σ R n) = psum τ R n := by
  calc
    rename e (psum σ R n) = ∑ i, (X (e i)) ^ n := by
      simp_rw [psum, map_sum, map_pow, rename_X]
    _ = ∑ i in univ.map e.toEmbedding, (X i) ^ n := by simp [-map_univ_equiv]
    _ = ∑ i, (X i) ^ n := by rw [map_univ_equiv]

theorem psum_isSymmetric (n : ℕ) : IsSymmetric (psum σ R n) := by
  intro
  rw [rename_psum]

end PowerSum

namespace Newton

open Finset Nat

variable (σ : Type _) [Fintype σ] [DecidableEq σ] [Fintype τ] (R : Type _) [CommRing R]
  [NoZeroDivisors (MvPolynomial σ R)] [CharZero (MvPolynomial σ R)]
/-
  TODO: show that MvPolynomial σ R is an integral domain if R is an integral domain
  TODO: show that MvPolynomial σ R has characteristic zero if R has characteristic zero
-/

-- The following proof is from Zeilberger, "A combinatorial proof of Newton's identities" (1984)
def PairsPred (k : ℕ) (t : Finset σ × σ) : Prop := card t.fst ≤ k ∧ (card t.fst = k → t.snd ∈ t.fst)

open Classical in
def pairs (σ : Type _) [Fintype σ] (k : ℕ) : Finset (Finset σ × σ) :=
  Finset.univ.filter (PairsPred σ k)

def weight (k : ℕ) (t : Finset σ × σ) : MvPolynomial σ R :=
  (-1) ^ (card t.fst) * ((∏ a in t.fst, X a) * (X t.snd) ^ (k - card t.fst) : MvPolynomial σ R)

def T_map (t : Finset σ × σ) : Finset σ × σ :=
  if t.snd ∈ t.fst then (t.fst.erase t.snd, t.snd) else (insert t.snd t.fst, t.snd)

/-- Needed for `Finset.sum_involution` -/
def T_map_restr (t : Finset σ × σ) (_ : t ∈ pairs σ k) := T_map σ t

open Classical in
theorem T_map_pair (t : Finset σ × σ) (h : t ∈ pairs σ k) : T_map_restr σ t h ∈ pairs σ k := by
  rw [pairs, mem_filter, PairsPred] at *
  simp_rw [T_map_restr, T_map]
  split_ifs with h1
  · simp_all
    apply And.intro
    · exact le_step h
    · by_contra h2
      have h3 : t.fst.Nonempty
      · use t.snd
        apply h1
      rw [← h2] at h
      exact not_le_of_lt (sub_lt (card_pos.mpr h3) zero_lt_one) h
  · simp_all
    simp_rw [card_insert_of_not_mem h1]
    exact Or.resolve_left (le_iff_eq_or_lt.mp h.1) h.2

theorem T_map_invol (t : Finset σ × σ) (h : t ∈ pairs σ k) :
    T_map_restr σ (T_map_restr σ t h) (T_map_pair σ t h) = t := by
  simp_rw [T_map_restr, T_map]
  split_ifs with h1 h2 h3
  · simp at h2
  · simp_rw [insert_erase h1]
  · simp_rw [erase_eq_self.mpr h1]
    simp_all
  · simp at h3

open Classical in
theorem weight_compose_T (t : Finset σ × σ) (h : t ∈ pairs σ k) :
    (weight σ R k t) + weight σ R k (T_map_restr σ t h) = 0 := by
  simp_rw [T_map_restr, T_map, weight]
  simp_rw [pairs, mem_filter, PairsPred] at h
  have h2 (n : ℕ) : -(-1 : MvPolynomial σ R) ^ n = (-1) ^ (n + 1)
  · rw [← neg_one_mul ((-1 : MvPolynomial σ R) ^ n), pow_add, pow_one, mul_comm]
  split_ifs with h1
  · simp_rw [card_erase_of_mem h1, ← prod_erase_mul t.fst (fun j ↦ (X j : MvPolynomial σ R)) h1,
      mul_comm, mul_assoc (∏ a in erase t.fst t.snd, X a), ← mul_add]
    nth_rewrite 1 [← pow_one (X t.snd)]
    simp_rw [← pow_add, add_comm]
    have h3 : card t.fst ≥ 1
    · have h4 : t.fst.Nonempty
      · use t.snd
        apply h1
      exact lt_iff_add_one_le.mp (card_pos.mpr h4)
    rw [← tsub_tsub_assoc h.right.left h3,
      ← neg_neg ((-1 : MvPolynomial σ R) ^ (card t.fst - 1)), h2 (card t.fst - 1),
      Nat.sub_add_cancel]
    simp
    exact h3
  · simp_rw [card_insert_of_not_mem h1, prod_insert h1, mul_comm, mul_assoc (∏ a in t.fst, X a),
      ← mul_add]
    nth_rewrite 2 [← pow_one (X t.snd)]
    have h3 : card t.fst + 1 ≤ k
    · have ht1 := h.right.right
      contrapose! ht1
      exact And.intro (le_antisymm h.right.left (le_of_lt_succ ht1)) h1
    simp_rw [← pow_add, ← Nat.add_sub_assoc h3, add_comm, add_tsub_add_eq_tsub_right]
    rw [← neg_neg ((-1 : MvPolynomial σ R) ^ (card t.fst)), h2]
    simp

theorem weight_zero_for_fixed_by_T (t : Finset σ × σ) (h : t ∈ pairs σ k)
    (h1 : weight σ R k t ≠ 0) : T_map_restr σ t h ≠ t := by
  by_contra h2
  have h3 := weight_compose_T σ R t h
  rw [h2, ← two_mul, _root_.mul_eq_zero] at h3
  cases' h3 with hl hr
  case inl => exact two_ne_zero hl
  case inr => exact h1 hr

theorem weight_sum (k : ℕ) : ∑ t in pairs σ k, weight σ R k t = 0 := by
  exact sum_involution (T_map_restr σ) (weight_compose_T σ R) (weight_zero_for_fixed_by_T σ R)
    (T_map_pair σ) (T_map_invol σ)

open Classical in
theorem sum_equiv_k (k : ℕ) (f : Finset σ × σ → MvPolynomial σ R) :
    (∑ t in filter (fun t ↦ card t.fst = k) (pairs σ k), f t) =
    ∑ A in powersetLen k univ, (∑ j in A, f (A, j)) := by
  apply sum_finset_product
  simp_all
  intro p b
  simp_rw [pairs, mem_filter, PairsPred]
  simp_all
  apply Iff.intro
  · intro hpl
    simp_all
    exact mem_powerset_len_univ_iff.mpr hpl.2
  · intro hpr
    simp_all
    have cardpk := mem_powerset_len_univ_iff.mp hpr.1
    exact And.intro (le_of_eq cardpk) cardpk

open Classical in
theorem sum_equiv_i_lt_k (k i : ℕ) (hi : i ∈ range k) (f : Finset σ × σ → MvPolynomial σ R) :
    (∑ t in filter (fun t ↦ card t.fst = i) (pairs σ k), f t) =
    ∑ A in powersetLen i univ, (∑ j, f (A, j)) := by
  apply sum_finset_product
  simp_all
  intro p b
  apply Iff.intro
  · intro hpl
    exact mem_powerset_len_univ_iff.mpr hpl.2
  · intro hpr
    simp_rw [pairs, mem_filter, PairsPred]
    simp_all
    apply And.intro
    · apply And.intro
      · simp_rw [mem_powerset_len_univ_iff.mp hpr, le_iff_lt_or_eq]
        left
        exact hi
      · intro cardpk
        rw [← cardpk, mem_powerset_len_univ_iff.mp hpr] at hi
        exact ((lt_irrefl _) hi).elim
    · exact mem_powerset_len_univ_iff.mp hpr

theorem sum_equiv_lt_k (k : ℕ) (f : Finset σ × σ → MvPolynomial σ R) :
    (∑ t in filter (fun t ↦ card t.fst < k) (pairs σ k), f t) =
    ∑ i in range k, ∑ A in powersetLen i univ, (∑ j, f (A, j)) := by
  have equiv_i (i : ℕ) (hi : i ∈ range k) := sum_equiv_i_lt_k σ R k i hi f
  simp_rw [← sum_congr rfl equiv_i]
  have pdisj : Set.PairwiseDisjoint (range k)
      (fun (i : ℕ) ↦ (filter (fun t ↦ card t.fst = i) (pairs σ k))) := by
    simp_rw [Set.PairwiseDisjoint, Set.Pairwise, Disjoint, pairs, filter_filter, PairsPred]
    simp
    intro x _ y _ xny
    by_contra neg
    simp at neg
    cases neg with
    | intro sneg hsneg =>
      simp_rw [subset_empty] at hsneg
      have sneg_ne := nonempty_iff_ne_empty.mpr hsneg.right.right
      rw [Finset.Nonempty] at sneg_ne
      cases sneg_ne with
      | intro s hs =>
        have hs1 := hsneg.left hs
        have hs2 := hsneg.right.left hs
        simp_rw [and_assoc, ← filter_filter, mem_filter] at hs1 hs2
        rw [← hs1.right, ← hs2.right] at xny
        exact xny rfl
  have hdisj := @sum_disjiUnion _ _ _ f _ (range k)
    (fun (i : ℕ) ↦ (filter (fun t ↦ card t.fst = i) (pairs σ k))) pdisj
  have disj_equiv : disjiUnion (range k) (fun i ↦ filter (fun t ↦ card t.fst = i) (pairs σ k))
      pdisj = filter (fun t ↦ card t.fst < k) (pairs σ k) := by
    apply Finset.ext
    intro a
    rw [mem_disjiUnion, mem_filter]
    apply Iff.intro
    · intro had
      cases had with
      | intro a1 ha1 =>
        rw [mem_filter] at ha1
        apply And.intro
        · exact ha1.right.left
        · rw [ha1.right.right]
          exact mem_range.mp ha1.left
    · intro haf
      use (card a.fst)
      apply And.intro
      · exact mem_range.mpr haf.right
      · simp_all [mem_filter]
  simp_rw [← hdisj, disj_equiv]

theorem lt_k_disjoint_k (k : ℕ) : Disjoint (filter (fun t ↦ card t.fst < k) (pairs σ k))
    (filter (fun t ↦ card t.fst = k) (pairs σ k)) := by
  rw [disjoint_filter]
  intro _ _ h1 h2
  rw [h2] at h1
  exact lt_irrefl _ h1

open Classical in
theorem lt_k_disjunion_k (k : ℕ) : disjUnion (filter (fun t ↦ card t.fst < k) (pairs σ k))
    (filter (fun t ↦ card t.fst = k) (pairs σ k)) (lt_k_disjoint_k σ k) = pairs σ k := by
  simp_all [← filter_or, Finset.ext_iff, pairs, PairsPred]
  intro a b ab _
  exact lt_or_eq_of_le ab

theorem esymm_summand_to_weight (k : ℕ) (A : Finset σ) (h : A ∈ powersetLen k univ) :
    ∑ j in A, weight σ R k (A, j) = k * (-1) ^ k * (∏ i in A, X i : MvPolynomial σ R) := by
  simp_all [weight, mem_powerset_len_univ_iff.mp h, mul_assoc]

theorem esymm_to_weight (k : ℕ) : k * esymm σ R k =
    (-1) ^ k * ∑ t in filter (fun t ↦ card t.fst = k) (pairs σ k), weight σ R k t := by
  rw [esymm, sum_equiv_k σ R k (fun t ↦ weight σ R k t),
    sum_congr rfl (esymm_summand_to_weight σ R k), mul_comm (k : MvPolynomial σ R) ((-1) ^ k),
    ← mul_sum, ← mul_assoc, ← mul_assoc, ← pow_add, Even.neg_one_pow]
  simp
  use k

theorem esymm_mul_psum_summand_to_weight (k i : ℕ) (_ : i ∈ range k) :
    ∑ A in powersetLen i univ, ∑ j, weight σ R k (A, j) =
    (-1) ^ i * esymm σ R i * psum σ R (k - i) := by
  simp_rw [esymm, psum, weight, ← mul_assoc, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl ?_
  intro x _
  rw [sum_mul]
  refine sum_congr rfl ?_
  intro x1 hx1
  simp_rw [mem_powerset_len_univ_iff.mp hx1]

theorem esymm_mul_psum_to_weight (k : ℕ) :
    ∑ i in range k, (-1) ^ i * esymm σ R i * psum σ R (k - i) =
    ∑ t in filter (fun t ↦ card t.fst < k) (pairs σ k), weight σ R k t := by
  simp_rw [← sum_congr rfl (esymm_mul_psum_summand_to_weight σ R k), sum_equiv_lt_k σ R k]

/-- Newton's identities give a recurrence relation for the kth elementary symmetric polynomial
in terms of lower degree elementary symmetric polynomials and power sums. -/
theorem esymm_recurrence (k : ℕ) : (-1) ^ k * (k * esymm σ R k) +
    ∑ i in range k, (-1) ^ i * esymm σ R i * psum σ R (k - i) = 0 := by
  simp_all [esymm_to_weight σ R k, esymm_mul_psum_to_weight σ R k, ← mul_assoc, ← pow_add,
    Even.neg_one_pow]
  rw [add_comm, ← sum_disjUnion (lt_k_disjoint_k σ k), lt_k_disjunion_k σ k, weight_sum σ R k]
