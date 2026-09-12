/-
Copyright (c) 2024 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, James Davenport, Michail Karatarakis
-/
module

public import Mathlib.Tactic.ComputablePolynomial.MvBasic
public import Mathlib.Data.List.Sort

/-!
# `MvSparsePoly`: construction from unsorted term lists, `X`, and monomial multiplication

`ofList` builds a canonical `MvSparsePoly` from an arbitrary term list by sorting and merging
(`dedupList`); `X v` is the sparse variable. `monomialMul` multiplies by a single monomial, and
`balancedSum` merges a list of polynomials as a balanced tree, the building block of the fast
multiplication.
-/

@[expose] public section

variable {nvars : ℕ}

namespace MvSparsePoly

open MvPolynomial

variable {R : Type} [CommRing R] [DecidableEq R]

/-- Merge adjacent equal-degree terms, summing coefficients. -/
def dedupList : List (MvDegrees nvars × R) → List (MvDegrees nvars × R)
  | (i, a) :: (j, b) :: x =>
    if i = j then
      dedupList ((i, a + b) :: x)
    else
      (i, a) :: dedupList ((j, b) :: x)
  | x => x

omit [DecidableEq R] in
lemma dedupList_bound : ∀ (terms : List (MvDegrees nvars × R)) (k : MvDegrees nvars),
    (∀ p ∈ terms, k ≥ p.1) → ∀ p ∈ dedupList terms, k ≥ p.1
  | [], k, h => by
    simp [dedupList]
  | [(i, a)], k, h => by
    intro x hx
    rw [show dedupList [(i, a)] = [(i, a)] by unfold dedupList; rfl] at hx
    exact h x hx
  | (i, a) :: (j, b) :: x, k, h => by
    unfold dedupList
    split
    · next heq =>
      apply dedupList_bound ((i, a + b) :: x) k
      intro p hp
      simp only [List.mem_cons] at hp
      rcases hp with rfl | hp_in_x
      · exact h (i, a) (by simp)
      · exact h p (by simp [hp_in_x])
    · next hneq =>
      intro p hp
      simp only [List.mem_cons] at hp
      rcases hp with rfl | hp_in_dedup
      · exact h (i, a) (by simp)
      · apply dedupList_bound ((j, b) :: x) k _ p hp_in_dedup
        intro p' hp'
        exact h p' (by simp [hp'])
termination_by terms => terms.length

omit [DecidableEq R] in
lemma dedupList_sorted_aux : ∀ (terms : List (MvDegrees nvars × R)),
    terms.Pairwise (fun p1 p2 => p2.1 ≤ p1.1) →
    (dedupList terms).Pairwise (fun p1 p2 => p2.1 < p1.1)
  | [] => fun _ => by unfold dedupList; constructor
  | [(i, a)] => fun _ => by
    rw [show dedupList [(i, a)] = [(i, a)] by unfold dedupList; rfl]
    constructor <;> grind
  | (i, a) :: (j, b) :: x => fun h => by
    unfold dedupList
    split
    · next heq =>
      have h_next : ((i, a + b) :: x).Pairwise (fun p1 p2 => p2.1 ≤ p1.1) := by
        simp only [List.pairwise_cons] at h ⊢
        rcases h with ⟨hi, hj_x⟩
        exact ⟨fun p hp => hi p (List.mem_cons_of_mem _ hp), by grind⟩
      exact dedupList_sorted_aux ((i, a + b) :: x) h_next
    · next hneq =>
      have ih := dedupList_sorted_aux ((j, b) :: x) h.of_cons
      simp only [List.pairwise_cons] at h ⊢
      rcases h with ⟨hi, hj_x⟩
      refine ⟨fun p hp => ?_, ih⟩
      have hj_bound : ∀ p' ∈ ((j, b) :: x), p'.1 ≤ j := by
        intro p' hp'
        simp only [List.mem_cons] at hp'
        rcases hp' with rfl | hp_x
        · exact le_rfl
        · exact hj_x.1 p' hp_x
      have hp_le_j : p.1 ≤ j := dedupList_bound ((j, b) :: x) j hj_bound p hp
      have j_lt_i : j < i := lt_of_le_of_ne (hi (j, b) List.mem_cons_self) (Ne.symm hneq)
      exact lt_of_le_of_lt hp_le_j j_lt_i
termination_by terms => terms.length

omit [DecidableEq R] in
theorem dedupList_sorted (terms : List (MvDegrees nvars × R))
  (sorted : terms.Pairwise (·.1 ≥ ·.1)) :
  (dedupList terms).Pairwise (·.1 > ·.1) := dedupList_sorted_aux terms sorted

/-- Sort an arbitrary term list and merge duplicate degrees into a canonical polynomial. -/
def ofList (terms : List (MvDegrees nvars × R)) : MvSparsePoly R nvars :=
  let terms' := terms.mergeSort (fun a b => decide (b.1 ≤ a.1))
  have hSorted : terms'.Pairwise (·.1 ≥ ·.1) := by
    apply List.Pairwise.imp (R := fun a b => decide (b.1 ≤ a.1) = true)
    · intro a b h
      change b.1 ≤ a.1
      exact of_decide_eq_true h
    · apply List.pairwise_mergeSort
      · exact fun a b c hab hbc =>
          decide_eq_true (le_trans (of_decide_eq_true hbc) (of_decide_eq_true hab))
      · intro a b
        rcases le_total b.1 a.1 with h1 | h2
        · simp only [decide_eq_true h1, Bool.true_or]
        · simp only [decide_eq_true h2, Bool.or_true]
  ofSortedList (dedupList terms') (dedupList_sorted terms' hSorted)

/-- Summing a list of zeros with exactly one entry set to `1` gives `1`. -/
lemma list_set_one_zero_foldl : ∀ (n : ℕ) (i : ℕ) (_h : i < n),
    ((List.replicate n 0).set i 1).foldl (· + ·) 0 = 1
  | 0, i, h => by omega
  | n + 1, 0, h => by
    change (1 :: List.replicate n 0).foldl (· + ·) 0 = 1
    rw [List.foldl_cons, list_foldl_add_acc (List.replicate n 0) (0 + 1),
      list_replicate_zero_foldl n]
  | n + 1, i + 1, h => by
    change (0 :: (List.replicate n 0).set i 1).foldl (· + ·) 0 = 1
    rw [List.foldl_cons]
    change ((List.replicate n 0).set i 1).foldl (· + ·) 0 = 1
    exact list_set_one_zero_foldl n i (by omega)


/-- The exponent vector of the single variable `v`: exponent `1` in position `v` and `0` elsewhere
(total degree `1`). -/
def singleDegree (v : Fin nvars) : MvDegrees nvars := {
  degrees := ((List.replicate nvars 0).set v.val 1).toArray
  correct := by simp
  totalDegree := 1
  totalDegree_eq := by
    symm
    simp only [← Array.foldl_toList]
    change ((List.replicate nvars 0).set v.val 1).foldl (· + ·) 0 = 1
    exact list_set_one_zero_foldl nvars v.val v.isLt
}

/-- The polynomial consisting of the single variable `v`. -/
def X (v : Fin nvars) : MvSparsePoly R nvars :=
  ofSortedList [(singleDegree v, 1)] (List.pairwise_singleton _ _)

/-- Exponent addition is right-cancellative (proved on the underlying arrays). -/
lemma mvDegrees_add_right_cancel {a b c : MvDegrees nvars} (h : a + c = b + c) : a = b := by
  have hd : a.degrees = b.degrees := by
    apply array_eq_of_toList_eq
    apply list_zipWith_add_right_cancel (lc := c.degrees.toList)
    · simp [a.correct, c.correct]
    · simp [b.correct, c.correct]
    · show List.zipWith (· + ·) a.degrees.toList c.degrees.toList
        = List.zipWith (· + ·) b.degrees.toList c.degrees.toList
      rw [← Array.toList_zipWith, ← Array.toList_zipWith]
      change (a + c).degrees.toList = (b + c).degrees.toList
      rw [h]
  obtain ⟨ad, hac, at_, hae⟩ := a
  obtain ⟨bd, hbc, bt, hbe⟩ := b
  subst hd
  simp only [MvDegrees.mk.injEq, true_and]
  rw [hae, hbe]

/-- Addition by a fixed exponent is strictly monotone in the monomial order. -/
lemma mvDegrees_add_lt_add_left {i j₁ j₂ : MvDegrees nvars} (h : j₂ < j₁) : i + j₂ < i + j₁ := by
  rw [add_comm i j₂, add_comm i j₁]
  refine lt_of_le_of_ne (WOrdering.add_le_add (le_of_lt h)) ?_
  intro he
  exact (ne_of_lt h) (mvDegrees_add_right_cancel he)

omit [DecidableEq R] in
lemma monomialMul_sorted (i : MvDegrees nvars) (a : R) (y : MvSparsePoly R nvars) :
    (y.terms.map (fun t => (i + t.1, a * t.2))).Pairwise (·.1 > ·.1) :=
  List.Pairwise.map _ (fun _ _ hpq => mvDegrees_add_lt_add_left hpq) y.sorted

/-- `monomialMul i a y = (a · Xⁱ) * y`, computed directly (no re-sort, since the result is
already sorted). The building block of the fast Johnson/Monagan–Pearce multiplication. -/
def monomialMul (i : MvDegrees nvars) (a : R) (y : MvSparsePoly R nvars) : MvSparsePoly R nvars :=
  ofSortedList (y.terms.map (fun t => (i + t.1, a * t.2))) (monomialMul_sorted i a y)

/-- Fuel-recursive worker for `balancedSum`: split the list in half and recurse, summing the two
halves. -/
def balancedSumGo : ℕ → List (MvSparsePoly R nvars) → MvSparsePoly R nvars
  | _, [] => 0
  | _, [p] => p
  | 0, l => l.foldl (· + ·) 0
  | fuel + 1, l => balancedSumGo fuel (l.take (l.length / 2)) +
    balancedSumGo fuel (l.drop (l.length / 2))

/-- Sum a list of polynomials by a balanced (divide-and-conquer) merge tree, so building an
`n`-term result costs `O(n log #summands)` merges instead of the `O(n · #summands)` of a left
fold. -/
def balancedSum (l : List (MvSparsePoly R nvars)) : MvSparsePoly R nvars :=
  balancedSumGo l.length l


end MvSparsePoly
