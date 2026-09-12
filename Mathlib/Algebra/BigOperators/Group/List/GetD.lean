/-
Copyright (c) 2026 Alessandro Iraci, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Aristotle (Harmonic)
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Data.List.GetD

/-!
# Sums of lists of natural numbers, indexed by position

A list of natural numbers can be summed as a list, or entry by entry through `List.getD`.
This file relates the two: the sum of a list is the sum over `Finset.range` of its entries,
partial sums are sums over an initial range, and the number of entries satisfying a predicate
is the cardinality of the corresponding subset of `Finset.range`.

## Main results

* `List.sum_eq_sum_range_getD` : `l.sum = ∑ i ∈ Finset.range k, l.getD i 0` for `l.length ≤ k`.
* `List.sum_take_eq_sum_range` : the same for the partial sums of `l`.
* `List.countP_eq_card_filter_range` : `l.countP p` counts the indices `i` with `p (l.getD i 0)`.
* `List.length_eq_sum_count` : the length of a list of letters `< M`, counted letter by letter.
-/

@[expose] public section

namespace List

/-! ### Bounds -/

/-- Coq `leq_head_sumn`. -/
lemma headD_le_sum (l : List ℕ) : l.headD 0 ≤ l.sum := by
  cases l with
  | nil => simp
  | cons a s => simp

/-- An entry of a list of natural numbers is at most the sum of the list. -/
lemma getD_le_sum (l : List ℕ) (i : ℕ) : l.getD i 0 ≤ l.sum := by
  rcases lt_or_ge i l.length with h | h
  · exact List.single_le_sum (fun _ _ => Nat.zero_le _) _ (by
      rw [List.getD_eq_getElem l 0 h]; exact List.getElem_mem h)
  · rw [List.getD_eq_default _ _ h]
    exact Nat.zero_le _

lemma sum_take_le_sum (l : List ℕ) (i : ℕ) : (l.take i).sum ≤ l.sum := by
  have h := List.sum_take_add_sum_drop l i
  omega

/-! ### Partial sums -/

lemma sum_take_succ_getD (l : List ℕ) (i : ℕ) :
    (l.take (i + 1)).sum = (l.take i).sum + l.getD i 0 := by
  induction l generalizing i with
  | nil => simp
  | cons a s ih =>
    cases i with
    | zero => simp
    | succ j => simp only [List.take_succ_cons, List.sum_cons, ih j, List.getD_cons_succ]; omega

lemma sum_tail_add_getD_zero (l : List ℕ) : l.tail.sum + l.getD 0 0 = l.sum := by
  cases l with
  | nil => simp
  | cons a s => simp [List.sum_cons]; omega

lemma sum_set_add_getElem (l : List ℕ) {j : ℕ} (h : j < l.length) (a : ℕ) :
    (l.set j a).sum + l[j] = l.sum + a := by
  induction l generalizing j with
  | nil => simp at h
  | cons x l ih =>
    cases j with
    | zero => simp; omega
    | succ m =>
      have := ih (j := m) (by simpa using h)
      simp only [List.set_cons_succ, List.sum_cons, List.getElem_cons_succ]
      omega

/-! ### Sums over `Finset.range` -/

lemma sum_take_eq_sum_range (l : List ℕ) (k : ℕ) :
    (l.take k).sum = ∑ i ∈ Finset.range k, l.getD i 0 := by
  induction k with
  | zero => simp
  | succ m ih => rw [sum_take_succ_getD, ih, Finset.sum_range_succ]

/-- The sum of a list of natural numbers as a sum of its parts. -/
lemma sum_eq_sum_range_getD_length (l : List ℕ) :
    l.sum = ∑ i ∈ Finset.range l.length, l.getD i 0 := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.sum_cons, ih, List.length_cons, Finset.sum_range_succ']
    simp [Nat.add_comm]

lemma sum_eq_sum_range_getD (l : List ℕ) {k : ℕ} (hk : l.length ≤ k) :
    l.sum = ∑ i ∈ Finset.range k, l.getD i 0 := by
  rw [sum_eq_sum_range_getD_length l]
  refine Finset.sum_subset
    (fun x hx => Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hx) hk))
    fun i _ hi => ?_
  exact List.getD_eq_default _ _ (by simpa using hi)

/-- Counting the elements of a list satisfying a predicate, by index. -/
lemma countP_eq_card_filter_range (l : List ℕ) (p : ℕ → Bool) :
    l.countP p = ((Finset.range l.length).filter (fun i ↦ p (l.getD i 0))).card := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.countP_cons, ih, List.length_cons, Finset.card_filter, Finset.card_filter,
      Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]

/-- The length of a list of letters `< M`, counted letter by letter. -/
lemma length_eq_sum_count {l : List ℕ} {M : ℕ} (h : ∀ x ∈ l, x < M) :
    l.length = ∑ i ∈ Finset.range M, l.count i := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha : a < M := h a (by simp)
    have hl : ∀ x ∈ l, x < M := fun x hx => h x (by simp [hx])
    have hcount : ∀ i, (a :: l).count i = l.count i + if a = i then 1 else 0 := by
      intro i
      rw [List.count_cons]
      by_cases hai : a = i <;> simp [hai]
    simp only [List.length_cons, ih hl]
    rw [Finset.sum_congr rfl (fun i _ => hcount i), Finset.sum_add_distrib,
      Finset.sum_ite_eq (Finset.range M) a (fun _ => 1), ite_eq_left (Finset.mem_range.2 ha)]

end List
