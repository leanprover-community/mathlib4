/-
Copyright (c) 2024 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.Data.List.Chain

/-!
# Group a list by a relation

This file provides the basic API for `List.groupBy`. The main results are the following:

- `List.join_groupBy`: the lists in `List.groupBy` join to the original list.
- `List.nil_not_mem_groupBy`: the empty list is not contained in `List.groupBy`.
- `List.chain'_of_mem_groupBy`: any two adjacent elements in a list in `List.groupBy` are related by
  the specified relation.
- `List.chain'_last_head_groupBy`: the last element of each list in `List.groupBy` is not related
  to the first element of the next list.
-/

namespace List

variable {α : Type*} {m : List α}

@[simp]
theorem groupBy_nil (r : α → α → Bool) : groupBy r [] = [] :=
  rfl

private theorem join_groupBy_loop (r : α → α → Bool) (l : List α) (a : α) (g : List α)
    (gs : List (List α)) :
    (groupBy.loop r l a g gs).join = gs.reverse.join ++ g.reverse ++ a::l := by
  revert a g gs
  induction l with
  | nil => simp [groupBy.loop]
  | cons b l IH =>
    intro a g gs
    rw [groupBy.loop]
    split <;> simp [IH]

@[simp]
theorem join_groupBy (r : α → α → Bool) (l : List α) : (l.groupBy r).join = l :=
  match l with
  | nil => rfl
  | cons _ _ => join_groupBy_loop _ _ _ _ _

private theorem nil_not_mem_groupBy_loop (r : α → α → Bool) (l : List α) (a : α) (g : List α)
    {gs : List (List α)} (h : [] ∉ gs) : [] ∉ groupBy.loop r l a g gs := by
  induction l generalizing a g gs with
  | nil =>
    simpa [groupBy.loop]
  | cons b l IH =>
    rw [groupBy.loop]
    split
    · exact IH _ _ h
    · apply IH
      simpa using h

theorem nil_not_mem_groupBy (r : α → α → Bool) (l : List α) : [] ∉ l.groupBy r :=
  match l with
  | nil => not_mem_nil _
  | cons _ _ => nil_not_mem_groupBy_loop _ _ _ _ <| not_mem_nil _

theorem ne_nil_of_mem_groupBy (r : α → α → Bool) {l : List α} (h : m ∈ l.groupBy r) : m ≠ [] := by
  rintro rfl
  exact nil_not_mem_groupBy r l h

private theorem chain'_of_mem_groupBy_loop {r : α → α → Bool} {l : List α} {a : α} {g : List α}
    (hga : ∀ b ∈ g.head?, r b a) (hg : g.Chain' fun y x ↦ r x y) {gs : List (List α)}
    (hgs : ∀ m ∈ gs, m.Chain' fun x y ↦ r x y) (h : m ∈ groupBy.loop r l a g gs) :
    m.Chain' fun x y ↦ r x y := by
  induction l generalizing a g gs with
  | nil =>
    rw [groupBy.loop, reverse_cons, mem_append, mem_reverse, mem_singleton] at h
    obtain hm | rfl := h
    · exact hgs m hm
    · apply List.chain'_reverse.1
      rw [reverse_reverse]
      exact chain'_cons'.2 ⟨hga, hg⟩
  | cons b l IH =>
    simp [groupBy.loop] at h
    split at h
    · apply IH _ (chain'_cons'.2 ⟨hga, hg⟩) hgs h
      intro b hb
      rw [head?_cons, Option.mem_some_iff] at hb
      rwa [← hb]
    · apply IH _ chain'_nil _ h
      · rintro _ ⟨⟩
      · intro m
        rw [mem_cons]
        rintro (rfl | hm)
        · apply List.chain'_reverse.1
          rw [reverse_append, reverse_cons, reverse_nil, nil_append, reverse_reverse]
          exact chain'_cons'.2 ⟨hga, hg⟩
        · exact hgs _ hm

theorem chain'_of_mem_groupBy {r : α → α → Bool} {l : List α} (h : m ∈ l.groupBy r) :
    m.Chain' fun x y ↦ r x y := by
  cases l with
  | nil => cases h
  | cons a l =>
    apply chain'_of_mem_groupBy_loop _ _ _ h
    · rintro _ ⟨⟩
    · exact chain'_nil
    · rintro _ ⟨⟩

private theorem chain'_last_head_groupBy_loop {r : α → α → Bool} (l : List α) {a : α}
    {g : List α} {gs : List (List α)} (hgs' : [] ∉ gs)
    (hgs : gs.Chain' fun b a ↦ ∃ ha hb, r (a.getLast ha) (b.head hb) = false)
    (hga : ∀ m ∈ gs.head?, ∃ ha hb, r (m.getLast ha) ((g.reverse ++ [a]).head hb) = false) :
    (groupBy.loop r l a g gs).Chain' fun a b ↦ ∃ ha hb, r (a.getLast ha) (b.head hb) = false := by
  induction l generalizing a g gs with
  | nil =>
    rw [groupBy.loop, reverse_cons]
    apply List.chain'_reverse.1
    simpa using chain'_cons'.2 ⟨hga, hgs⟩
  | cons b l IH =>
    rw [groupBy.loop]
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

theorem chain'_last_head_groupBy (r : α → α → Bool) (l : List α) :
    (l.groupBy r).Chain' fun a b ↦ ∃ ha hb, r (a.getLast ha) (b.head hb) = false := by
  cases l with
  | nil => exact chain'_nil
  | cons _ _ =>
    apply chain'_last_head_groupBy_loop _ (not_mem_nil _) chain'_nil
    rintro _ ⟨⟩

end List
