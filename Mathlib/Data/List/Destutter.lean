/-
Copyright (c) 2022 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez, Eric Wieser
-/
import Mathlib.Data.List.Chain

/-!
# Destuttering of Lists

This file proves theorems about `List.destutter` (in `Data.List.Defs`), which greedily removes all
non-related items that are adjacent in a list, e.g. `[2, 2, 3, 3, 2].destutter (≠) = [2, 3, 2]`.
Note that we make no guarantees of being the longest sublist with this property; e.g.,
`[123, 1, 2, 5, 543, 1000].destutter (<) = [123, 543, 1000]`, but a longer ascending chain could be
`[1, 2, 5, 543, 1000]`.

## Main statements

* `List.destutter_sublist`: `l.destutter` is a sublist of `l`.
* `List.destutter_is_chain'`: `l.destutter` satisfies `Chain' R`.
* Analogies of these theorems for `List.destutter'`, which is the `destutter` equivalent of `Chain`.

## Tags

adjacent, chain, duplicates, remove, list, stutter, destutter
-/


variable {α : Type*} (l : List α) (R : α → α → Prop) [DecidableRel R] {a b : α}

namespace List

@[simp]
theorem destutter'_nil : destutter' R a [] = [a] :=
  rfl

theorem destutter'_cons :
    (b :: l).destutter' R a = if R a b then a :: destutter' R b l else destutter' R a l :=
  rfl

variable {R}

@[simp]
theorem destutter'_cons_pos (h : R b a) : (a :: l).destutter' R b = b :: l.destutter' R a := by
  rw [destutter', if_pos h]

@[simp]
theorem destutter'_cons_neg (h : ¬R b a) : (a :: l).destutter' R b = l.destutter' R b := by
  rw [destutter', if_neg h]

variable (R)

@[simp]
theorem destutter'_singleton : [b].destutter' R a = if R a b then [a, b] else [a] := by
  split_ifs with h <;> simp! [h]

theorem destutter'_sublist (a) : l.destutter' R a <+ a :: l := by
  induction' l with b l hl generalizing a
  · simp
  rw [destutter']
  split_ifs
  · exact Sublist.cons₂ a (hl b)
  · exact (hl a).trans ((l.sublist_cons b).cons_cons a)

theorem mem_destutter' (a) : a ∈ l.destutter' R a := by
  induction' l with b l hl
  · simp
  rw [destutter']
  split_ifs
  · simp
  · assumption

theorem destutter'_is_chain : ∀ l : List α, ∀ {a b}, R a b → (l.destutter' R b).Chain R a
  | [], a, b, h => chain_singleton.mpr h
  | c :: l, a, b, h => by
    rw [destutter']
    split_ifs with hbc
    · rw [chain_cons]
      exact ⟨h, destutter'_is_chain l hbc⟩
    · exact destutter'_is_chain l h

theorem destutter'_is_chain' (a) : (l.destutter' R a).Chain' R := by
  induction' l with b l hl generalizing a
  · simp
  rw [destutter']
  split_ifs with h
  · exact destutter'_is_chain R l h
  · exact hl a

theorem destutter'_of_chain (h : l.Chain R a) : l.destutter' R a = a :: l := by
  induction' l with b l hb generalizing a
  · simp
  obtain ⟨h, hc⟩ := chain_cons.mp h
  rw [l.destutter'_cons_pos h, hb hc]

@[simp]
theorem destutter'_eq_self_iff (a) : l.destutter' R a = a :: l ↔ l.Chain R a :=
  ⟨fun h => by
    suffices Chain' R (a::l) by
      assumption
    rw [← h]
    exact l.destutter'_is_chain' R a, destutter'_of_chain _ _⟩

theorem destutter'_ne_nil : l.destutter' R a ≠ [] :=
  ne_nil_of_mem <| l.mem_destutter' R a

@[simp]
theorem destutter_nil : ([] : List α).destutter R = [] :=
  rfl

theorem destutter_cons' : (a :: l).destutter R = destutter' R a l :=
  rfl

theorem destutter_cons_cons :
    (a :: b :: l).destutter R = if R a b then a :: destutter' R b l else destutter' R a l :=
  rfl

@[simp]
theorem destutter_singleton : destutter R [a] = [a] :=
  rfl

@[simp]
theorem destutter_pair : destutter R [a, b] = if R a b then [a, b] else [a] :=
  destutter_cons_cons _ R

theorem destutter_sublist : ∀ l : List α, l.destutter R <+ l
  | [] => Sublist.slnil
  | h :: l => l.destutter'_sublist R h

theorem destutter_is_chain' : ∀ l : List α, (l.destutter R).Chain' R
  | [] => List.chain'_nil
  | h :: l => l.destutter'_is_chain' R h

theorem destutter_of_chain' : ∀ l : List α, l.Chain' R → l.destutter R = l
  | [], _ => rfl
  | _ :: l, h => l.destutter'_of_chain _ h

@[simp]
theorem destutter_eq_self_iff : ∀ l : List α, l.destutter R = l ↔ l.Chain' R
  | [] => by simp
  | a :: l => l.destutter'_eq_self_iff R a

theorem destutter_idem : (l.destutter R).destutter R = l.destutter R :=
  destutter_of_chain' R _ <| l.destutter_is_chain' R

@[simp]
theorem destutter_eq_nil : ∀ {l : List α}, destutter R l = [] ↔ l = []
  | [] => Iff.rfl
  | _ :: l => ⟨fun h => absurd h <| l.destutter'_ne_nil R, fun h => nomatch h⟩

end List
