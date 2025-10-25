/-
Copyright (c) 2024 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Flatten

/-!
# Split a list into contiguous runs of elements which pairwise satisfy a relation.

This file provides the basic API for `List.splitBy` which is defined in Core.
The main results are the following:

- `List.flatten_splitBy`: the lists in `List.splitBy` join to the original list.
- `List.nil_notMem_splitBy`: the empty list is not contained in `List.splitBy`.
- `List.isChain_of_mem_splitBy`: any two adjacent elements in a list in
  `List.splitBy` are related by the specified relation.
- `List.isChain_getLast_head_splitBy`: the last element of each list in `List.splitBy` is not
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

@[simp]
theorem splitBy_eq_nil {r : α → α → Bool} {l : List α} : l.splitBy r = [] ↔ l = [] := by
  have := flatten_splitBy r l
  refine ⟨fun _ ↦ ?_, ?_⟩ <;> simp_all

theorem splitBy_ne_nil {r : α → α → Bool} {l : List α} : l.splitBy r ≠ [] ↔ l ≠ [] :=
  splitBy_eq_nil.not

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

@[simp]
theorem nil_notMem_splitBy (r : α → α → Bool) (l : List α) : [] ∉ l.splitBy r :=
  match l with
  | nil => not_mem_nil
  | cons _ _ => nil_notMem_splitByLoop

@[deprecated (since := "2025-05-23")] alias nil_not_mem_splitBy := nil_notMem_splitBy

theorem ne_nil_of_mem_splitBy {r : α → α → Bool} {l : List α} (h : m ∈ l.splitBy r) : m ≠ [] := by
  rintro rfl
  exact nil_notMem_splitBy r l h

theorem head_head_splitBy (r : α → α → Bool) {l : List α} (hn : l ≠ []) :
    ((l.splitBy r).head (splitBy_ne_nil.2 hn)).head
      (ne_nil_of_mem_splitBy (head_mem _)) = l.head hn := by
  simp_rw [← head_flatten_of_head_ne_nil, flatten_splitBy]

theorem getLast_getLast_splitBy (r : α → α → Bool) {l : List α} (hn : l ≠ []) :
    ((l.splitBy r).getLast (splitBy_ne_nil.2 hn)).getLast
      (ne_nil_of_mem_splitBy (getLast_mem _)) = l.getLast hn := by
  simp_rw [← getLast_flatten_of_getLast_ne_nil, flatten_splitBy]

private theorem isChain_of_mem_splitByLoop {r : α → α → Bool} {l : List α} {a : α} {g : List α}
    (hga : ∀ b ∈ g.head?, r b a) (hg : g.IsChain fun y x ↦ r x y)
    (h : m ∈ splitBy.loop r l a g []) : m.IsChain fun x y ↦ r x y := by
  induction l generalizing a g with
  | nil =>
    rw [splitBy.loop, reverse_cons, mem_append, mem_reverse, mem_singleton] at h
    obtain hm | rfl := h
    · exact (not_mem_nil hm).elim
    · apply List.isChain_reverse.1
      rw [reverse_reverse]
      exact isChain_cons.2 ⟨hga, hg⟩
  | cons b l IH =>
    simp only [splitBy.loop, reverse_cons] at h
    split at h
    · apply IH _ (isChain_cons.2 ⟨hga, hg⟩) h
      intro b hb
      rw [head?_cons, Option.mem_some_iff] at hb
      rwa [← hb]
    · rw [splitByLoop_eq_append, mem_append, reverse_singleton, mem_singleton] at h
      obtain rfl | hm := h
      · apply List.isChain_reverse.1
        rw [reverse_append, reverse_cons, reverse_nil, nil_append, reverse_reverse]
        exact isChain_cons.2 ⟨hga, hg⟩
      · apply IH _ isChain_nil hm
        rintro _ ⟨⟩

theorem isChain_of_mem_splitBy {r : α → α → Bool} {l : List α} (h : m ∈ l.splitBy r) :
    m.IsChain fun x y ↦ r x y := by
  cases l with
  | nil => cases h
  | cons a l =>
    apply isChain_of_mem_splitByLoop _ _ h
    · rintro _ ⟨⟩
    · exact isChain_nil

@[deprecated (since := "2025-09-24")] alias chain'_of_mem_splitBy := isChain_of_mem_splitBy

private theorem isChain_getLast_head_splitByLoop {r : α → α → Bool} (l : List α) {a : α}
    {g : List α} {gs : List (List α)} (hgs' : [] ∉ gs)
    (hgs : gs.IsChain fun b a ↦ ∃ ha hb, r (a.getLast ha) (b.head hb) = false)
    (hga : ∀ m ∈ gs.head?, ∃ ha hb, r (m.getLast ha) ((g.reverse ++ [a]).head hb) = false) :
    (splitBy.loop r l a g gs).IsChain fun a b ↦ ∃ ha hb, r (a.getLast ha) (b.head hb) = false := by
  induction l generalizing a g gs with
  | nil =>
    rw [splitBy.loop, reverse_cons]
    apply List.isChain_reverse.1
    simpa using isChain_cons.2 ⟨hga, hgs⟩
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
        apply isChain_cons.2 ⟨hga, hgs⟩
      · simpa

theorem isChain_getLast_head_splitBy (r : α → α → Bool) (l : List α) :
    (l.splitBy r).IsChain fun a b ↦ ∃ ha hb, r (a.getLast ha) (b.head hb) = false := by
  cases l with
  | nil => exact isChain_nil
  | cons _ _ =>
    apply isChain_getLast_head_splitByLoop _ not_mem_nil isChain_nil
    rintro _ ⟨⟩

private theorem splitByLoop_append {r : α → α → Bool} {l g : List α} {a : α}
    (h : (g.reverse ++ a :: l).IsChain fun x y ↦ r x y)
    (ha : ∀ x ∈ m.head?, r ((a :: l).getLast (cons_ne_nil a l)) x = false) :
    splitBy.loop r (l ++ m) a g [] = (g.reverse ++ a :: l) :: m.splitBy r := by
  induction l generalizing a g with
  | nil =>
    rw [nil_append]
    cases m with
    | nil => simp [splitBy.loop]
    | cons c m => simp_all [splitBy.loop, splitByLoop_eq_append [_], splitBy]
  | cons b l IH => simp_all [splitBy.loop]

theorem splitBy_of_isChain {r : α → α → Bool} {l : List α} (hn : l ≠ [])
    (h : l.IsChain fun x y ↦ r x y) : splitBy r l = [l] := by
  cases l with
  | nil => contradiction
  | cons a l => rw [splitBy, ← append_nil l, splitByLoop_append] <;> simp [h]

private theorem splitBy_append_of_isChain {r : α → α → Bool} {l : List α} (hn : l ≠ [])
    (h : l.IsChain fun x y ↦ r x y) (ha : ∀ x ∈ m.head?, r (l.getLast hn) x = false) :
    (l ++ m).splitBy r = l :: m.splitBy r := by
  cases l with
  | nil => contradiction
  | cons a l => rw [cons_append, splitBy, splitByLoop_append h ha]; simp

theorem splitBy_flatten {r : α → α → Bool} {l : List (List α)} (hn : [] ∉ l)
    (hc : ∀ m ∈ l, m.IsChain fun x y ↦ r x y)
    (hc' : l.IsChain fun a b ↦ ∃ ha hb, r (a.getLast ha) (b.head hb) = false) :
    l.flatten.splitBy r = l := by
  induction l with
  | nil => rfl
  | cons a l IH =>
    rw [mem_cons, not_or, eq_comm] at hn
    rw [flatten_cons, splitBy_append_of_isChain hn.1 (hc _ mem_cons_self),
      IH hn.2 (fun m hm ↦ hc _ (mem_cons_of_mem a hm)) hc'.tail]
    intro y hy
    rw [← head_of_mem_head? hy]
    rw [isChain_cons] at hc'
    obtain ⟨x, hx, _⟩ := flatten_ne_nil_iff.1 (ne_nil_of_mem (mem_of_mem_head? hy))
    obtain ⟨_, _, H⟩ := hc'.1 (l.head (ne_nil_of_mem hx)) (head_mem_head? _)
    rwa [head_flatten_of_head_ne_nil]

/-- A characterization of `splitBy m r` as the unique list `l` such that:

* The lists of `l` join to `m`.
* It does not contain the empty list.
* Every list in `l` is `IsChain` of `r`.
* The last element of each list in `l` is not related by `r` to the head of the next.
-/
theorem splitBy_eq_iff {r : α → α → Bool} {l : List (List α)} :
    m.splitBy r = l ↔ m = l.flatten ∧ [] ∉ l ∧ (∀ m ∈ l, m.IsChain fun x y ↦ r x y) ∧
      l.IsChain fun a b ↦ ∃ ha hb, r (a.getLast ha) (b.head hb) = false := by
  constructor
  · rintro rfl
    exact ⟨(flatten_splitBy r m).symm, nil_notMem_splitBy r m, fun _ ↦ isChain_of_mem_splitBy,
      isChain_getLast_head_splitBy r m⟩
  · rintro ⟨rfl, hn, hc, hc'⟩
    exact splitBy_flatten hn hc hc'

theorem splitBy_append {r : α → α → Bool} {l : List α}
    (ha : ∀ x ∈ l.getLast?, ∀ y ∈ m.head?, r x y = false) :
    (l ++ m).splitBy r = l.splitBy r ++ m.splitBy r := by
  obtain rfl | hl := eq_or_ne l []
  · simp
  obtain rfl | hm := eq_or_ne m []
  · simp
  rw [splitBy_eq_iff]
  refine ⟨by simp, by simp, ?_, ?_⟩
  · aesop (add apply unsafe isChain_of_mem_splitBy)
  rw [isChain_append]
  refine ⟨isChain_getLast_head_splitBy _ _, isChain_getLast_head_splitBy _ _, fun x hx y hy ↦ ?_⟩
  use ne_nil_of_mem_splitBy (mem_of_mem_getLast? hx), ne_nil_of_mem_splitBy (mem_of_mem_head? hy)
  apply ha
  · simp_rw [← getLast_of_mem_getLast? hx, getLast_getLast_splitBy _ hl]
    exact getLast_mem_getLast? _
  · simp_rw [← head_of_mem_head? hy, head_head_splitBy _ hm]
    exact head_mem_head? _

theorem splitBy_append_cons {r : α → α → Bool} {l : List α} {a : α} (m : List α)
    (ha : ∀ x ∈ l.getLast?, r x a = false) :
    (l ++ a :: m).splitBy r = l.splitBy r ++ (a :: m).splitBy r := by
  apply splitBy_append
  simpa

@[deprecated (since := "2025-09-24")]
alias chain'_getLast_head_splitBy := isChain_getLast_head_splitBy

end List
