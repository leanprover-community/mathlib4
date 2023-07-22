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
import Mathlib.RingTheory.MvPolynomial.Symmetric

/-!
# Newton's Identities

This file defines `MvPolynomial` power sums as a means of implementing Newton's identities.

## Main declarations

## Notation

+ `psum σ R n`, is the degree-`n` power sum in `MvPolynomial σ R`.

As in other polynomial files, we typically use the notation:

+ `σ τ : Type _` (indexing the variables)

+ `R S : Type _` `[CommSemiring R]` `[CommSemiring S]` (the coefficients)

+ `r : R` elements of the coefficient ring

+ `i : σ`, with corresponding monomial `X i`, often denoted `X_i` by mathematicians

+ `φ ψ : MvPolynomial σ R`

-/

open Equiv (Perm)

open BigOperators MvPolynomial

noncomputable section

section PowerSum

namespace Multiset

variable {R : Type _} [CommSemiring R]

/-- The degree-`n` power sum evaluated at the elements of `s` -/
def psum (s : Multiset R) (n : ℕ) : R :=
  (s.map (fun (x : R) ↦ x^n)).sum

end Multiset

open Finset

variable (σ R) [CommSemiring R] [Fintype σ] [Fintype τ]

/-- The degree-`n` power sum -/
def psum (n : ℕ) : MvPolynomial σ R := ∑ i in univ, (X i)^n

theorem rename_psum (n : ℕ) (e : σ ≃ τ) : rename e (psum σ R n) = psum τ R n := by
  calc
    rename e (psum σ R n) = ∑ i in univ, (X (e i))^n := by
      simp_rw [psum, map_sum, map_pow, rename_X]
    _ = ∑ i in univ.map e.toEmbedding, (X i)^n := by simp [-map_univ_equiv]
    _ = ∑ i in univ, (X i)^n := by rw [map_univ_equiv]

theorem psum_isSymmetric (n : ℕ) : IsSymmetric (psum σ R n) := by
  intro
  rw [rename_psum]

end PowerSum

section Newton

open Classical Finset Nat

variable (σ : Type) [Fintype σ] [DecidableEq σ] [Fintype τ] (R : Type) [CommRing R]
  [NoZeroDivisors (MvPolynomial σ R)] [CharZero (MvPolynomial σ R)]
/-
  TODO: show that MvPolynomial σ R is an integral domain if R is an integral domain
  TODO: show that MvPolynomial σ R has characteristic zero if R has characteristic zero
-/

def fintype_card (σ : Type) [Fintype σ] := Finset.card (univ : Finset σ)

/-- The following proof is from Zeilberger, "A combinatorial proof of Newton's identities" (1983) -/
def j_in_A_pred (t : Finset σ × σ) := t.snd ∈ t.fst
def pairs_pred (k : ℕ) (t : Finset σ × σ) := card t.fst ≤ k ∧ (card t.fst = k → j_in_A_pred σ t)

/-- We need set membership to be decidable, which it is not in the constructivist paradigm -/
instance : DecidablePred (j_in_A_pred σ) := inferInstance

def pairs (σ : Type) [Fintype σ] (k : ℕ) : Finset (Finset σ × σ) :=
  Finset.univ.filter (pairs_pred σ k)

def weight (k : ℕ) (t : Finset σ × σ) : MvPolynomial σ R :=
  (-1)^(card t.fst)*((∏ a in t.fst, X a)*(X t.snd)^(k-card t.fst) : MvPolynomial σ R)

def T_map (t : Finset σ × σ) : Finset σ × σ :=
  if t.snd ∈ t.fst then (t.fst.erase t.snd, t.snd) else (insert t.snd t.fst, t.snd)

/-- Needed for Finset.sum_involution -/
def T_map_restr (t : Finset σ × σ) (_ : t ∈ pairs σ k) := T_map σ t

theorem T_map_pair (t : Finset σ × σ) (h : t ∈ pairs σ k) : T_map_restr σ t h ∈ pairs σ k := by
  rw [pairs, mem_filter, pairs_pred, j_in_A_pred]
  rw [pairs, mem_filter, pairs_pred, j_in_A_pred] at h
  simp_rw [T_map_restr, T_map]
  split_ifs with h1
  · simp_all
    simp_rw [card_erase_of_mem h1]
    apply And.intro
    · simp
      exact le_trans h (le_succ k)
    · by_contra h2
      have h3 : t.1.Nonempty
      · use t.2
        apply h1
      rw [← h2] at h
      exact not_le_of_lt (sub_lt (card_pos.mpr h3) zero_lt_one) h
  · simp
    simp_rw [card_insert_of_not_mem h1]
    have ht1 := h.2.2
    contrapose! ht1
    apply And.intro
    · exact le_antisymm h.2.1 (le_of_lt_succ ht1)
    · exact h1

theorem T_map_invol (t : Finset σ × σ) (h : t ∈ pairs σ k) :
    T_map_restr σ (T_map_restr σ t h) (T_map_pair σ t h) = t := by
  simp_rw [T_map_restr, T_map]
  split_ifs with h1 h2 h3
  · simp at h2
  · simp_rw [insert_erase h1]
  · simp
    simp_rw [erase_eq_self.mpr h1]
  · simp at h3

theorem weight_compose_T (t : Finset σ × σ) (h : t ∈ pairs σ k) :
    (weight σ R k t) + weight σ R k (T_map_restr σ t h) = 0 := by
  simp_rw [T_map_restr, T_map, weight]
  simp_rw [pairs, mem_filter, pairs_pred, j_in_A_pred] at h
  split_ifs with h1
  · simp
    simp_rw [card_erase_of_mem h1, ← prod_erase_mul t.1 (fun j => (X j : MvPolynomial σ R)) h1,
      mul_comm, mul_assoc]
    sorry
  · simp
    simp_rw [card_insert_of_not_mem h1, prod_insert h1, mul_comm, mul_assoc]
    sorry

theorem weight_zero_for_fixed_by_T (t : Finset σ × σ) (h : t ∈ pairs σ k)
    (h1 : weight σ R k t ≠ 0) : T_map_restr σ t h ≠ t := by
  by_contra h2
  have h3 := weight_compose_T σ R t h
  rw [h2, ← two_mul, _root_.mul_eq_zero] at h3
  cases' h3 with hl hr
  case inl => exact two_ne_zero hl
  case inr => exact h1 hr

theorem sum_equiv (k : ℕ) (f : Finset σ × σ → MvPolynomial σ R) :
    (∑ t in Finset.filter (fun t => card t.1 = k) (pairs σ k), f t) =
    ∑ A in powersetLen k univ, (∑ j in A, f (A, j)) := by
  sorry

theorem esymm_summand_to_weight (k : ℕ) (A : Finset σ) (h : A ∈ powersetLen k univ) :
    ∑ j in A, weight σ R k (A, j) = k * (-1)^k * (∏ i in A, X i : MvPolynomial σ R) := by
  simp_rw [weight, _root_.pow_zero, mem_powerset_len_univ_iff.mp h]
  simp
  rw [mem_powerset_len_univ_iff.mp h, mul_assoc]

theorem esymm_to_weight (k : ℕ) : k * esymm σ R k =
    (-1)^k * ∑ t in Finset.filter (fun t => card t.1 = k) (pairs σ k), weight σ R k t := by
  simp_rw [esymm]
  rw [sum_equiv σ R k (fun t => weight σ R k t)]
  rw [sum_congr rfl (esymm_summand_to_weight σ R k)]
  sorry

theorem psum_to_weight (k i : ℕ) : true := sorry

theorem weight_sum (k : ℕ) : ∑ t in pairs σ k, weight σ R k t = 0 := by
  exact sum_involution (T_map_restr σ) (weight_compose_T σ R) (weight_zero_for_fixed_by_T σ R)
    (T_map_pair σ) (T_map_invol σ)

theorem NewtonIdentityLE (k : ℕ) (h1 : 1 ≤ k) (h2 : k ≤ fintype_card σ) :
    k * esymm σ R k - ∑ i in range k, (-1)^(i - 1) * esymm σ R (k - i) * psum σ R i = 0 := by
  simp_rw [fintype_card]
  sorry

theorem NewtonIdentityGT (k : ℕ) (h1 : fintype_card σ ≥ 1) (h2 : k > fintype_card σ) :
    ∑ i in Icc (k - fintype_card σ) k, (-1)^(i - 1) * esymm σ R (k - i) * psum σ R i = 0 := by
  simp_rw [fintype_card]
  sorry
