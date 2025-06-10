/-
Copyright (c) 2024 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.Data.List.Chain

/-!
# Split a list into contiguous runs of elements which pairwise satisfy a relation.

This file provides the basic API for `List.splitBy` which is defined in Core.
The main results are the following:

- `List.join_splitBy`: the lists in `List.splitBy` join to the original list.
- `List.nil_notMem_splitBy`: the empty list is not contained in `List.splitBy`.
- `List.chain'_of_mem_splitBy`: any two adjacent elements in a list in `List.splitBy` are related by
  the specified relation.
- `List.chain'_getLast_head_splitBy`: the last element of each list in `List.splitBy` is not
  related to the first element of the next list.
-/

namespace List

variable {α : Type*} {m : List α}

@[simp]
theorem splitBy_nil (r : α → α → Bool) : splitBy r [] = [] :=
  rfl

private theorem splitByLoop_eq_append {r : α → α → Bool} {l : List α} {a : α} {g : List α}
    (gs : List (List α)) : splitBy.loop r l a g gs = gs.reverse ++ splitBy.loop r l a g [] := by
  induction l generalizing a g gs with
  | nil => simp [splitBy.loop]
  | cons b l IH =>
    simp_rw [splitBy.loop]
    split <;> rw [IH]
    conv_rhs => rw [IH]
    simp

private theorem flatten_splitByLoop {r : α → α → Bool} {l : List α} {a : α} {g : List α} :
    (splitBy.loop r l a g []).flatten = g.reverse ++ a :: l := by
  induction l generalizing a g with
  | nil => simp [splitBy.loop]
  | cons b l IH =>
    rw [splitBy.loop, splitByLoop_eq_append [_]]
    split <;> simp [IH]

@[simp]
theorem flatten_splitBy (r : α → α → Bool) (l : List α) : (l.splitBy r).flatten = l :=
  match l with
  | nil => rfl
  | cons _ _ => flatten_splitByLoop

private theorem nil_notMem_splitByLoop {r : α → α → Bool} {l : List α} {a : α} {g : List α} :
    [] ∉ splitBy.loop r l a g [] := by
  induction l generalizing a g with
  | nil =>
    simp [splitBy.loop]
  | cons b l IH =>
    rw [splitBy.loop]
    split
    · exact IH
    · rw [splitByLoop_eq_append, mem_append]
      simpa using IH

@[deprecated (since := "2025-05-23")] alias nil_not_mem_splitByLoop := nil_notMem_splitByLoop

theorem nil_notMem_splitBy (r : α → α → Bool) (l : List α) : [] ∉ l.splitBy r :=
  match l with
  | nil => not_mem_nil
  | cons _ _ => nil_notMem_splitByLoop

@[deprecated (since := "2025-05-23")] alias nil_not_mem_splitBy := nil_notMem_splitBy

theorem ne_nil_of_mem_splitBy (r : α → α → Bool) {l : List α} (h : m ∈ l.splitBy r) : m ≠ [] := by
  rintro rfl
  exact nil_notMem_splitBy r l h

private theorem chain'_of_mem_splitByLoop {r : α → α → Bool} {l : List α} {a : α} {g : List α}
    (hga : ∀ b ∈ g.head?, r b a) (hg : g.Chain' fun y x ↦ r x y)
    (h : m ∈ splitBy.loop r l a g []) : m.Chain' fun x y ↦ r x y := by
  induction l generalizing a g with
  | nil =>
    rw [splitBy.loop, reverse_cons, mem_append, mem_reverse, mem_singleton] at h
    obtain hm | rfl := h
    · exact (not_mem_nil hm).elim
    · apply List.chain'_reverse.1
      rw [reverse_reverse]
      exact chain'_cons'.2 ⟨hga, hg⟩
  | cons b l IH =>
    simp only [splitBy.loop, reverse_cons] at h
    split at h
    · apply IH _ (chain'_cons'.2 ⟨hga, hg⟩) h
      intro b hb
      rw [head?_cons, Option.mem_some_iff] at hb
      rwa [← hb]
    · rw [splitByLoop_eq_append, mem_append, reverse_singleton, mem_singleton] at h
      obtain rfl | hm := h
      · apply List.chain'_reverse.1
        rw [reverse_append, reverse_cons, reverse_nil, nil_append, reverse_reverse]
        exact chain'_cons'.2 ⟨hga, hg⟩
      · apply IH _ chain'_nil hm
        rintro _ ⟨⟩

theorem chain'_of_mem_splitBy {r : α → α → Bool} {l : List α} (h : m ∈ l.splitBy r) :
    m.Chain' fun x y ↦ r x y := by
  cases l with
  | nil => cases h
  | cons a l =>
    apply chain'_of_mem_splitByLoop _ _ h
    · rintro _ ⟨⟩
    · exact chain'_nil

private theorem chain'_getLast_head_splitByLoop {r : α → α → Bool} (l : List α) {a : α}
    {g : List α} {gs : List (List α)} (hgs' : [] ∉ gs)
    (hgs : gs.Chain' fun b a ↦ ∃ ha hb, r (a.getLast ha) (b.head hb) = false)
    (hga : ∀ m ∈ gs.head?, ∃ ha hb, r (m.getLast ha) ((g.reverse ++ [a]).head hb) = false) :
    (splitBy.loop r l a g gs).Chain' fun a b ↦ ∃ ha hb, r (a.getLast ha) (b.head hb) = false := by
  induction l generalizing a g gs with
  | nil =>
    rw [splitBy.loop, reverse_cons]
    apply List.chain'_reverse.1
    simpa using chain'_cons'.2 ⟨hga, hgs⟩
  | cons b l IH =>
    rw [splitBy.loop]
    split
    · apply IH hgs' hgs
      intro m hm
      obtain ⟨ha, _, H⟩ := hga m hm
      refine ⟨ha, append_ne_nil_of_right_ne_nil _ (cons_ne_nil _ _), ?_⟩
      rwa [reverse_cons, head_append_of_ne_nil]
    · apply IH
      · simpa using hgs'
      · rw [reverse_cons]
        apply chain'_cons'.2 ⟨hga, hgs⟩
      · simpa

theorem chain'_getLast_head_splitBy (r : α → α → Bool) (l : List α) :
    (l.splitBy r).Chain' fun a b ↦ ∃ ha hb, r (a.getLast ha) (b.head hb) = false := by
  cases l with
  | nil => exact chain'_nil
  | cons _ _ =>
    apply chain'_getLast_head_splitByLoop _ not_mem_nil chain'_nil
    rintro _ ⟨⟩

@[deprecated (since := "2024-10-30")] alias groupBy_nil := splitBy_nil
@[deprecated (since := "2024-10-30")] alias flatten_groupBy := flatten_splitBy
@[deprecated (since := "2024-10-30")] alias nil_not_mem_groupBy := nil_notMem_splitBy
@[deprecated (since := "2024-10-30")] alias ne_nil_of_mem_groupBy := ne_nil_of_mem_splitBy
@[deprecated (since := "2024-10-30")] alias chain'_of_mem_groupBy := chain'_of_mem_splitBy
@[deprecated (since := "2024-10-30")]
alias chain'_getLast_head_groupBy := chain'_getLast_head_splitBy

end List
