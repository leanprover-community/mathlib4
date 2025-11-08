/-
Copyright (c) 2024 Daniel Weber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Weber
-/
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Order.MinMax

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
theorem length_splitLengths : (sz.splitLengths l).length = sz.length := by
  induction sz generalizing l <;> simp [splitLengths, *]

@[simp]
lemma splitLengths_nil : [].splitLengths l = [] := rfl

@[simp]
lemma splitLengths_cons (n : ℕ) :
    (n :: sz).splitLengths l = l.take n :: sz.splitLengths (l.drop n) := by
  simp [splitLengths]

theorem take_splitLength (i : ℕ) : (sz.splitLengths l).take i = (sz.take i).splitLengths l := by
  induction i generalizing sz l
  case zero => simp
  case succ i hi =>
    cases sz
    · simp
    · simp only [splitLengths_cons, take_succ_cons, hi]

theorem length_splitLengths_getElem_le {i : ℕ} {hi : i < (sz.splitLengths l).length} :
    (sz.splitLengths l)[i].length ≤ sz[i]'(by simpa using hi) := by
  induction sz generalizing l i
  · simp at hi
  case cons head tail tail_ih =>
    simp only [splitLengths_cons]
    cases i
    · simp
    · simp only [getElem_cons_succ, tail_ih]

theorem flatten_splitLengths (h : l.length ≤ sz.sum) : (sz.splitLengths l).flatten = l := by
  induction sz generalizing l
  · simp_all
  case cons head tail ih =>
    simp only [splitLengths_cons, flatten_cons]
    rw [ih, take_append_drop]
    simpa [add_comm] using h

theorem map_splitLengths_length (h : sz.sum ≤ l.length) :
    (sz.splitLengths l).map length = sz := by
  induction sz generalizing l
  · simp
  case cons head tail ih =>
    simp only [sum_cons] at h
    simp only [splitLengths_cons, map_cons, length_take, cons.injEq, min_eq_left_iff]
    rw [ih]
    · simp [Nat.le_of_add_right_le h]
    · simp [Nat.le_sub_of_add_le' h]

theorem length_splitLengths_getElem_eq {i : ℕ} (hi : i < sz.length)
    (h : (sz.take (i + 1)).sum ≤ l.length) :
    ((sz.splitLengths l)[i]'(by simpa)).length = sz[i] := by
  rw [List.getElem_take' (hj := i.lt_add_one)]
  simp only [take_splitLength]
  conv_rhs =>
    rw [List.getElem_take' (hj := i.lt_add_one)]
    simp +singlePass only [← map_splitLengths_length l _ h]
    rw [getElem_map]

theorem splitLengths_length_getElem {α : Type*} (l : List α) (sz : List ℕ)
    (h : sz.sum ≤ l.length) (i : ℕ) (hi : i < (sz.splitLengths l).length) :
    (sz.splitLengths l)[i].length = sz[i]'(by simpa using hi) := by
  have := map_splitLengths_length l sz h
  rw [← List.getElem_map List.length]
  · simp [this]
  · simpa using hi

theorem length_mem_splitLengths {α : Type*} (l : List α) (sz : List ℕ) (b : ℕ)
    (h : ∀ n ∈ sz, n ≤ b) : ∀ l₂ ∈ sz.splitLengths l, l₂.length ≤ b := by
  rw [← List.forall_getElem]
  intro i hi
  have := length_splitLengths_getElem_le l sz (hi := hi)
  have := h (sz[i]'(by simpa using hi)) (getElem_mem ..)
  cutsat

end List
