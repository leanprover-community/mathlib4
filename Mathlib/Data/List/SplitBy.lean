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
- `List.nil_not_mem_splitBy`: the empty list is not contained in `List.splitBy`.
- `List.chain'_of_mem_splitBy`: any two adjacent elements in a list in `List.splitBy` are related by
  the specified relation.
- `List.chain'_getLast_head_splitBy`: the last element of each list in `List.splitBy` is not
  related to the first element of the next list.
-/

namespace List

variable {α : Type*} {m : List α}

theorem head_eq_of_mem_head? {x} (hx : x ∈ m.head?) :
    m.head (ne_nil_of_mem (mem_of_mem_head? hx)) = x := by
  cases m
  · contradiction
  · simpa using hx

theorem getLast_eq_of_mem_getLast? {x} (hx : x ∈ m.getLast?) :
    m.getLast (ne_nil_of_mem (mem_of_mem_getLast? hx)) = x := by
  rw [Option.mem_def] at hx
  cases m
  · contradiction
  · rw [← Option.some_inj, ← hx]
    rfl

@[simp]
theorem splitBy_nil (r : α → α → Bool) : splitBy r [] = [] :=
  rfl

@[simp]
theorem splitBy_singleton (r : α → α → Bool) (a : α) : splitBy r [a] = [[a]] :=
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
theorem splitBy_eq_nil_iff {r : α → α → Bool} {l : List α} : l.splitBy r = [] ↔ l = [] := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · have := flatten_splitBy r l
    rwa [h, flatten_nil, eq_comm] at this
  · rintro rfl
    rfl

theorem splitBy_ne_nil_iff {r : α → α → Bool} {l : List α} : l.splitBy r ≠ [] ↔ l ≠ [] :=
  splitBy_eq_nil_iff.not

private theorem nil_not_mem_splitByLoop {r : α → α → Bool} {l : List α} {a : α} {g : List α} :
    [] ∉ splitBy.loop r l a g [] := by
  induction l generalizing a g with
  | nil => simp [splitBy.loop]
  | cons b l IH =>
    rw [splitBy.loop]
    split
    · exact IH
    · rw [splitByLoop_eq_append, mem_append]
      simpa using IH

@[simp]
theorem nil_not_mem_splitBy (r : α → α → Bool) (l : List α) : [] ∉ l.splitBy r :=
  match l with
  | nil => not_mem_nil _
  | cons _ _ => nil_not_mem_splitByLoop

theorem ne_nil_of_mem_splitBy {r} {l : List α} (h : m ∈ l.splitBy r) : m ≠ [] := by
  rintro rfl
  exact nil_not_mem_splitBy r l h

theorem head_head_splitBy (r : α → α → Bool) {l : List α} (hn : l ≠ []) :
    ((l.splitBy r).head (splitBy_ne_nil_iff.2 hn)).head
      (ne_nil_of_mem_splitBy (head_mem _)) = l.head hn := by
  simp_rw [← head_flatten_of_head_ne_nil, flatten_splitBy]

theorem getLast_getLast_splitBy (r : α → α → Bool) {l : List α} (hn : l ≠ []) :
    ((l.splitBy r).getLast (splitBy_ne_nil_iff.2 hn)).getLast
      (ne_nil_of_mem_splitBy (getLast_mem _)) = l.getLast hn := by
  simp_rw [← getLast_flatten_of_getLast_ne_nil, flatten_splitBy]

private theorem chain'_of_mem_splitByLoop {r : α → α → Bool} {l : List α} {a : α} {g : List α}
    (hga : ∀ b ∈ g.head?, r b a) (hg : g.Chain' fun y x ↦ r x y)
    (h : m ∈ splitBy.loop r l a g []) : m.Chain' fun x y ↦ r x y := by
  induction l generalizing a g with
  | nil =>
    rw [splitBy.loop, reverse_cons, mem_append, mem_reverse, mem_singleton] at h
    obtain hm | rfl := h
    · cases not_mem_nil m hm
    · rw [List.chain'_reverse]
      exact chain'_cons'.2 ⟨hga, hg⟩
  | cons b l IH =>
    simp [splitBy.loop] at h
    split at h
    · refine IH (fun b hb ↦ ?_) (chain'_cons'.2 ⟨hga, hg⟩) h
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
    apply chain'_getLast_head_splitByLoop _ (not_mem_nil _) chain'_nil
    rintro _ ⟨⟩

private theorem splitByLoop_append {r : α → α → Bool} {l g : List α} {a : α}
    (h : (g.reverse ++ a :: l).Chain' fun x y ↦ r x y)
    (ha : ∀ x ∈ m.head?, r ((a :: l).getLast (cons_ne_nil a l)) x = false) :
    splitBy.loop r (l ++ m) a g [] = (g.reverse ++ a :: l) :: m.splitBy r := by
  induction l generalizing a g with
  | nil =>
    rw [nil_append]
    cases m with
    | nil => simp [splitBy.loop]
    | cons c m => simp_all [splitBy.loop, ha c rfl, splitByLoop_eq_append [_], splitBy]
  | cons b l IH => simp_all [splitBy.loop]

set_option linter.docPrime false in
theorem splitBy_of_chain' {r : α → α → Bool} {l : List α} (hn : l ≠ [])
    (h : l.Chain' fun x y ↦ r x y) : splitBy r l = [l] := by
  cases l with
  | nil => contradiction
  | cons a l => rw [splitBy, ← append_nil l, splitByLoop_append] <;> simp [h]

private theorem splitBy_append_of_chain' {r : α → α → Bool} {l : List α} (hn : l ≠ [])
    (h : l.Chain' fun x y ↦ r x y) (ha : ∀ x ∈ m.head?, r (l.getLast hn) x = false) :
    (l ++ m).splitBy r = l :: m.splitBy r := by
  cases l with
  | nil => contradiction
  | cons a l =>
    rw [cons_append, splitBy, splitByLoop_append h ha]; simp

theorem splitBy_flatten {r : α → α → Bool} {l : List (List α)} (hn : [] ∉ l)
    (hc : ∀ m ∈ l, m.Chain' fun x y ↦ r x y)
    (hc' : l.Chain' fun a b ↦ ∃ ha hb, r (a.getLast ha) (b.head hb) = false) :
    l.flatten.splitBy r = l := by
  induction l with
  | nil => rfl
  | cons a l IH =>
    rw [mem_cons, not_or, eq_comm] at hn
    rw [flatten_cons, splitBy_append_of_chain' hn.1 (hc _ (mem_cons_self a l)),
      IH hn.2 (fun m hm ↦ hc _ (mem_cons_of_mem a hm)) hc'.tail]
    intro y hy
    rw [← head_eq_of_mem_head? hy]
    rw [chain'_cons'] at hc'
    obtain ⟨x, hx, _⟩ := flatten_ne_nil_iff.1 (ne_nil_of_mem (mem_of_mem_head? hy))
    obtain ⟨_, _, H⟩ := hc'.1 (l.head (ne_nil_of_mem hx)) (head_mem_head? _)
    rwa [head_flatten_of_head_ne_nil]

/-- A characterization of `splitBy m r` as the unique list `l` such that:
* The lists of `l` join to `m`.
* It does not contain the empty list.
* Every list in `l` is `Chain'` of `r`.
* The last element of each list in `l` is not related by `r` to the head of the next.
-/
theorem splitBy_eq_iff {r : α → α → Bool} {l : List (List α)} :
    m.splitBy r = l ↔ m = l.flatten ∧ [] ∉ l ∧ (∀ m ∈ l, m.Chain' fun x y ↦ r x y) ∧
      l.Chain' fun a b ↦ ∃ ha hb, r (a.getLast ha) (b.head hb) = false := by
  constructor
  · rintro rfl
    exact ⟨(flatten_splitBy r m).symm, nil_not_mem_splitBy r m, fun _ ↦ chain'_of_mem_splitBy,
      chain'_getLast_head_splitBy r m⟩
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
  · aesop (add apply unsafe chain'_of_mem_splitBy)
  rw [chain'_append]
  refine ⟨chain'_getLast_head_splitBy _ _, chain'_getLast_head_splitBy _ _, fun x hx y hy ↦ ?_⟩
  use ne_nil_of_mem_splitBy (mem_of_mem_getLast? hx), ne_nil_of_mem_splitBy (mem_of_mem_head? hy)
  apply ha
  · simp_rw [← getLast_eq_of_mem_getLast? hx, getLast_getLast_splitBy _ hl]
    exact getLast_mem_getLast? _
  · simp_rw [← head_eq_of_mem_head? hy, head_head_splitBy _ hm]
    exact head_mem_head? _

theorem splitBy_append_cons {r : α → α → Bool} {l : List α} {a : α} (m : List α)
    (ha : ∀ x ∈ l.getLast?, r x a = false) :
    (l ++ a :: m).splitBy r = l.splitBy r ++ (a :: m).splitBy r := by
  apply splitBy_append
  simpa

@[deprecated (since := "2024-10-30")] alias groupBy_nil := splitBy_nil
@[deprecated (since := "2024-10-30")] alias flatten_groupBy := flatten_splitBy
@[deprecated (since := "2024-10-15")] alias join_splitBy := flatten_splitBy
@[deprecated (since := "2024-10-30")] alias nil_not_mem_groupBy := nil_not_mem_splitBy
@[deprecated (since := "2024-10-30")] alias ne_nil_of_mem_groupBy := ne_nil_of_mem_splitBy
@[deprecated (since := "2024-10-30")] alias chain'_of_mem_groupBy := chain'_of_mem_splitBy
@[deprecated (since := "2024-10-30")]
alias chain'_getLast_head_groupBy := chain'_getLast_head_splitBy

end List
