/-
Copyright (c) 2024 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.Data.List.Chain
import Mathlib.Logic.Function.Defs

/-!
# Group a list by a relation

This file provides the basic API for `List.groupBy`. We show that its elements are non-empty and
related by the specified relation. We show that the `List.join` of `List.groupBy` yields the
original list.
-/


namespace List

variable {α : Type*} (r : α → α → Bool) (l : List α) {m : List α}

@[simp]
theorem groupBy_nil : groupBy r [] = [] :=
  rfl

theorem nil_not_mem_groupBy_loop (a : α) (g : List α) {gs : List (List α)} (h : [] ∉ gs) :
    [] ∉ groupBy.loop r l a g gs := by
  revert a g gs
  induction l with
  | nil =>
      intro a g gs
      simp [groupBy.loop]
  | cons b l IH =>
      intro a g gs h
      rw [groupBy.loop]
      split
      · exact IH _ _ h
      · apply IH
        simpa using h

theorem nil_not_mem_groupBy : [] ∉ l.groupBy r :=
  match l with
  | nil => not_mem_nil _
  | cons _ _ => nil_not_mem_groupBy_loop _ _ _ _ <| not_mem_nil _

theorem ne_nil_of_mem_groupBy (h : m ∈ l.groupBy r) : m ≠ [] := by
  rintro rfl
  exact nil_not_mem_groupBy r l h

theorem chain'_of_mem_groupBy_loop (a : α) {g : List α} (hga : ∀ b ∈ g.head?, r b a)
    (hg : g.Chain' (fun x y ↦ r y x)) {gs : List (List α)}
    (hgs : ∀ m ∈ gs, m.Chain' (fun x y ↦ r x y)) (h : m ∈ groupBy.loop r l a g gs) :
    m.Chain' (fun x y ↦ r x y) := by
  revert a g gs
  induction l with
  | nil =>
      intro a g hga hg gs hgs h
      rw [groupBy.loop, reverse_cons, mem_append, mem_reverse, mem_singleton] at h
      obtain hm | rfl := h
      · exact hgs m hm
      · apply List.chain'_reverse.1
        rw [reverse_reverse]
        exact chain'_cons'.2 ⟨hga, hg⟩
  | cons b l IH =>
      intro a g hga hg gs hgs h
      simp [groupBy.loop] at h
      split at h
      · apply IH _ _ (chain'_cons'.2 ⟨hga, hg⟩) hgs h
        intro b hb
        rw [head?_cons, Option.mem_some_iff] at hb
        rwa [← hb]
      · apply IH _ _ chain'_nil _ h
        · rintro _ ⟨⟩
        · intro m
          rw [mem_cons]
          rintro (rfl | hm)
          · apply List.chain'_reverse.1
            rw [reverse_append, reverse_cons, reverse_nil, nil_append, reverse_reverse]
            exact chain'_cons'.2 ⟨hga, hg⟩
          · apply hgs _ hm

theorem chain'_of_mem_groupBy (h : m ∈ l.groupBy r) : m.Chain' (fun x y ↦ r x y) := by
  cases l with
  | nil => cases h
  | cons a l =>
      apply chain'_of_mem_groupBy_loop r l a _ _ _ h
      · rintro _ ⟨⟩
      · exact chain'_nil
      · rintro _ ⟨⟩

theorem join_groupBy_loop (a : α) (g : List α) (gs : List (List α)) :
    (groupBy.loop r l a g gs).join = gs.reverse.join ++ g.reverse ++ a::l := by
  revert a g gs
  induction l with
  | nil => simp [groupBy.loop]
  | cons b l IH =>
      intro a g gs
      rw [groupBy.loop]
      split <;>
      simp [IH]

@[simp]
theorem join_groupBy : (l.groupBy r).join = l :=
  match l with
  | nil => rfl
  | cons _ _ => join_groupBy_loop _ _ _ _ _

theorem chain'_last_ne_head_groupBy_loop (a : α) (g : List α) {gs : List (List α)} (hgs' : [] ∉ gs)
    (hgs : gs.Chain' (fun b a ↦ ∃ ha hb, r (a.getLast ha) (b.head hb) = false))
    (hga : ∀ m ∈ gs.head?, ∃ ha hb, r (m.getLast ha) ((g.reverse ++ [a]).head hb) = false) :
    (groupBy.loop r l a g gs).Chain' (fun a b ↦ ∃ ha hb, r (a.getLast ha) (b.head hb) = false) := by
  revert a g gs
  induction l with
  | nil =>
      intro a g gs hgs' hgs hga
      rw [groupBy.loop]
      simp
      apply List.chain'_reverse.1
      simp
      exact chain'_cons'.2 ⟨hga, hgs⟩
  | cons b l IH =>
      intro a g gs hgs' hgs hga
      rw [groupBy.loop]
      split
      · apply IH _ _ hgs' hgs
        intro m hm
        obtain ⟨ha, _, H⟩ := hga m hm
        use ha
        have : (a :: g).reverse ++ [b] ≠ [] := by
          apply append_ne_nil_of_right_ne_nil
          exact cons_ne_nil _ _
        refine ⟨this, ?_⟩
        simp only [reverse_cons]
        rwa [head_append_of_ne_nil]
      · apply IH
        · simpa using hgs'
        · simp
          apply chain'_cons'.2
          constructor
          · exact hga
          · exact hgs
        · simpa

theorem chain'_last_ne_head_groupBy :
    (l.groupBy r).Chain' (fun a b ↦ ∃ ha hb, r (a.getLast ha) (b.head hb) = false) := by
  cases l with
  | nil => exact chain'_nil
  | cons _ _ =>
      apply chain'_last_ne_head_groupBy_loop _ _ _ _ (not_mem_nil _) chain'_nil
      rintro _ ⟨⟩ 

end List
