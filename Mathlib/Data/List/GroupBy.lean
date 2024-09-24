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

private theorem groupBy_loop_eq_append {r : α → α → Bool} {l : List α} {a : α} {g : List α}
    (gs : List (List α)) : groupBy.loop r l a g gs = gs.reverse ++ groupBy.loop r l a g [] := by
  induction l generalizing a g gs with
  | nil => simp [groupBy.loop]
  | cons b l IH =>
    simp_rw [groupBy.loop]
    split <;> rw [IH]
    conv_rhs => rw [IH]
    simp

private theorem join_groupBy_loop {r : α → α → Bool} {l : List α} {a : α} {g : List α} :
    (groupBy.loop r l a g []).join = g.reverse ++ a :: l := by
  induction l generalizing a g with
  | nil => simp [groupBy.loop]
  | cons b l IH =>
    rw [groupBy.loop, groupBy_loop_eq_append [_]]
    split <;> simp [IH]

@[simp]
theorem join_groupBy (r : α → α → Bool) (l : List α) : (l.groupBy r).join = l :=
  match l with
  | nil => rfl
  | cons _ _ => join_groupBy_loop

@[simp]
theorem groupBy_eq_nil {r : α → α → Bool} {l : List α} : l.groupBy r = [] ↔ l = [] := by
  constructor
  · intro h
    have := join_groupBy r l
    rwa [h, join_nil, eq_comm] at this
  · rintro rfl
    rfl

private theorem nil_not_mem_groupBy_loop {r : α → α → Bool} {l : List α} {a : α} {g : List α} :
    [] ∉ groupBy.loop r l a g [] := by
  induction l generalizing a g with
  | nil =>
    simp [groupBy.loop]
  | cons b l IH =>
    rw [groupBy.loop]
    split
    · exact IH
    · rw [groupBy_loop_eq_append, mem_append]
      simpa using IH

theorem nil_not_mem_groupBy (r : α → α → Bool) (l : List α) : [] ∉ l.groupBy r :=
  match l with
  | nil => not_mem_nil _
  | cons _ _ => nil_not_mem_groupBy_loop

theorem ne_nil_of_mem_groupBy (r : α → α → Bool) {l : List α} (h : m ∈ l.groupBy r) : m ≠ [] := by
  rintro rfl
  exact nil_not_mem_groupBy r l h

private theorem chain'_of_mem_groupBy_loop {r : α → α → Bool} {l : List α} {a : α} {g : List α}
    (hga : ∀ b ∈ g.head?, r b a) (hg : g.Chain' fun y x ↦ r x y)
    (h : m ∈ groupBy.loop r l a g []) : m.Chain' fun x y ↦ r x y := by
  induction l generalizing a g with
  | nil =>
    rw [groupBy.loop, reverse_cons, mem_append, mem_reverse, mem_singleton] at h
    obtain hm | rfl := h
    · exact (not_mem_nil m hm).elim
    · apply List.chain'_reverse.1
      rw [reverse_reverse]
      exact chain'_cons'.2 ⟨hga, hg⟩
  | cons b l IH =>
    simp [groupBy.loop] at h
    split at h
    · apply IH _ (chain'_cons'.2 ⟨hga, hg⟩) h
      intro b hb
      rw [head?_cons, Option.mem_some_iff] at hb
      rwa [← hb]
    · rw [groupBy_loop_eq_append, mem_append, reverse_singleton, mem_singleton] at h
      obtain rfl | hm := h
      · apply List.chain'_reverse.1
        rw [reverse_append, reverse_cons, reverse_nil, nil_append, reverse_reverse]
        exact chain'_cons'.2 ⟨hga, hg⟩
      · apply IH _ chain'_nil hm
        rintro _ ⟨⟩

theorem chain'_of_mem_groupBy {r : α → α → Bool} {l : List α} (h : m ∈ l.groupBy r) :
    m.Chain' fun x y ↦ r x y := by
  cases l with
  | nil => cases h
  | cons a l =>
    apply chain'_of_mem_groupBy_loop _ _ h
    · rintro _ ⟨⟩
    · exact chain'_nil

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

private theorem groupBy_loop_append {r : α → α → Bool} {l g : List α} {a : α}
    (h : (g.reverse ++ a :: l).Chain' fun x y ↦ r x y)
    (ha : ∀ h : m ≠ [], r ((a :: l).getLast (cons_ne_nil a l)) (m.head h) = false) :
    groupBy.loop r (l ++ m) a g [] = (g.reverse ++ a :: l) :: m.groupBy r := by
  induction l generalizing a g with
  | nil =>
    rw [nil_append]
    cases m with
    | nil => simp [groupBy.loop]
    | cons c m  =>
      rw [groupBy.loop]
      have := ha (cons_ne_nil c m)
      rw [getLast_singleton, head_cons] at this
      rw [this, groupBy_loop_eq_append [_], groupBy]
      simp
  | cons b l IH =>
    rw [cons_append, groupBy.loop]
    split
    · rw [IH]
      · simp
      · simp [h]
      · rwa [getLast_cons (cons_ne_nil b l)] at ha
    · rw [chain'_append_cons_cons, ← Bool.ne_false_iff] at h
      have := h.2.1
      contradiction

theorem groupBy_of_chain' {r : α → α → Bool} {l : List α} (hn : l ≠ [])
    (h : l.Chain' fun x y ↦ r x y) : groupBy r l = [l] := by
  cases l with
  | nil => contradiction
  | cons a l => rw [groupBy, ← append_nil l, groupBy_loop_append] <;> simp [h]

theorem groupBy_append {r : α → α → Bool} {l : List α} (hn : l ≠ [])
    (h : l.Chain' fun x y ↦ r x y) (ha : ∀ h : m ≠ [], r (l.getLast hn) (m.head h) = false) :
    (l ++ m).groupBy r = l :: m.groupBy r := by
  cases l with
  | nil => contradiction
  | cons a l => rw [cons_append, groupBy, groupBy_loop_append] <;> simp [h, ha]

theorem groupBy_append_cons {r : α → α → Bool} {l : List α} (hn : l ≠ []) {a : α} (m : List α)
    (h : l.Chain' fun x y ↦ r x y) (ha : r (l.getLast hn) a = false) :
    (l ++ a :: m).groupBy r = l :: (a :: m).groupBy r := by
  apply groupBy_append hn h
  intros
  rwa [head_cons]

theorem join_head {l : List (List α)} (hl : l ≠ []) (hl' : l.head hl ≠ []) :
    l.join.head ((join_ne_nil _).2 ⟨_, head_mem hl, hl'⟩) = (l.head hl).head hl' := by
  cases l with
  | nil => contradiction
  | cons a l =>
    simp_rw [join_cons, head_cons]
    exact head_append_of_ne_nil _

theorem head_mem_head? : ∀ {l : List α} (h : l ≠ []), head l h ∈ head? l
  | [], h => by contradiction
  | a :: l, _ => rfl

theorem groupBy_join {r : α → α → Bool} {l : List (List α)} (hn : [] ∉ l)
    (hc : ∀ m ∈ l, m.Chain' fun x y ↦ r x y)
    (hc' : l.Chain' fun a b ↦ ∃ ha hb, r (a.getLast ha) (b.head hb) = false) :
    l.join.groupBy r = l := by
  induction l with
  | nil => rfl
  | cons a l IH =>
    rw [mem_cons, not_or, eq_comm] at hn
    rw [join_cons, groupBy_append hn.1 (hc _ (mem_cons_self a l)), IH hn.2 _ hc'.tail]
    · intro m hm
      exact hc _ (mem_cons_of_mem a hm)
    · intro h
      rw [chain'_cons'] at hc'
      obtain ⟨x, hx, _⟩ := (join_ne_nil _).1 h
      obtain ⟨_, _, H⟩ := hc'.1 (l.head (ne_nil_of_mem hx)) (head_mem_head? _)
      rwa [join_head]

theorem groupBy_eq_iff {r : α → α → Bool} {l : List (List α)} :
    m.groupBy r = l ↔ l.join = m ∧ [] ∉ l ∧ (∀ m ∈ l, m.Chain' fun x y ↦ r x y) ∧
      l.Chain' fun a b ↦ ∃ ha hb, r (a.getLast ha) (b.head hb) = false := by
  constructor
  · rintro rfl
    exact ⟨join_groupBy r m, nil_not_mem_groupBy r m, fun _ ↦ chain'_of_mem_groupBy,
      chain'_last_head_groupBy r m⟩
  · rintro ⟨rfl, hn, hc, hc'⟩
    exact groupBy_join hn hc hc'

end List
