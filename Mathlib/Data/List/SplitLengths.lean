/-
Copyright (c) 2024 Daniel Weber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Weber
-/
import Mathlib.Data.List.Join
import Mathlib.Order.MinMax
import Mathlib.Algebra.BigOperators.Group.List

/-!
# Splitting a list to chunks of specified lengths

This file defines splitting a list to chunks of given lengths, and some proofs about that.
-/

variable {α : Type*} (l : List α) (sz : List ℕ)

namespace List

/--
Split a list to chunks of given lengths.
-/
def splitLengths : List ℕ → List α → List (List α)
  | [], _ => []
  | n::ns, x =>
    let (x0, x1) := x.splitAt n
    x0 :: ns.splitLengths x1

@[simp]
theorem length_splitLengths :
    (sz.splitLengths l).length = sz.length := by
  induction sz generalizing l
  · simp [splitLengths]
  · simp [splitLengths, ‹∀ (l : List α), _›]

theorem length_splitLengths_getElem {i : ℕ} {hi : i < (sz.splitLengths l).length} :
    (sz.splitLengths l)[i].length ≤ sz[i]'(by simpa using hi) := by
  induction sz generalizing l i
  · simp at hi
  case cons head tail tail_ih =>
    simp only [splitLengths, splitAt_eq]
    cases i
    · simp
    · simp only [getElem_cons_succ]
      apply tail_ih

theorem join_splitLengths (h : l.length ≤ sz.sum) : (sz.splitLengths l).join = l := by
  induction sz generalizing l
  · simp_all [splitLengths]
  case cons head tail ih =>
    simp only [splitLengths, splitAt_eq, join_cons]
    rw [ih, take_append_drop]
    simpa [add_comm] using h

theorem splitLengths_map_length (h : sz.sum ≤ l.length) :
    (sz.splitLengths l).map length = sz := by
  induction sz generalizing l
  · simp_all [splitLengths]
  case cons head tail ih =>
    simp only [sum_cons] at h
    simp only [splitLengths, splitAt_eq, map_cons, length_take, cons.injEq, min_eq_left_iff]
    rw [ih]
    · simp [Nat.le_of_add_right_le h]
    · simp [Nat.le_sub_of_add_le' h]

theorem splitLengths_length_getElem {α : Type*} (l : List α) (sz : List ℕ)
    (h : sz.sum ≤ l.length) (i : ℕ) (hi : i < (sz.splitLengths l).length) :
    (sz.splitLengths l)[i].length = sz[i]'(by simpa using hi) := by
  have := splitLengths_map_length l sz h
  rw [← List.getElem_map List.length]
  · simp [this]
  · simpa using hi

theorem length_mem_splitLengths {α : Type*} (l : List α) (sz : List ℕ) (b : ℕ)
    (h : ∀ n ∈ sz, n ≤ b) : ∀ l₂ ∈ sz.splitLengths l, l₂.length ≤ b := by
  rw [← List.forall_getElem]
  intro i hi
  have := length_splitLengths_getElem l sz (hi := hi)
  have := h (sz[i]'(by simpa using hi)) (getElem_mem ..)
  omega

end List
