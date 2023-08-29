/-
Copyright (c) 2022 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez, Eric Wieser
-/
import Mathlib.Data.List.Chain

#align_import data.list.destutter from "leanprover-community/mathlib"@"7b78d1776212a91ecc94cf601f83bdcc46b04213"

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
#align list.destutter'_nil List.destutter'_nil

theorem destutter'_cons :
    (b :: l).destutter' R a = if R a b then a :: destutter' R b l else destutter' R a l :=
  rfl
#align list.destutter'_cons List.destutter'_cons

variable {R}

@[simp]
theorem destutter'_cons_pos (h : R b a) : (a :: l).destutter' R b = b :: l.destutter' R a := by
  rw [destutter', if_pos h]
  -- 🎉 no goals
#align list.destutter'_cons_pos List.destutter'_cons_pos

@[simp]
theorem destutter'_cons_neg (h : ¬R b a) : (a :: l).destutter' R b = l.destutter' R b := by
  rw [destutter', if_neg h]
  -- 🎉 no goals
#align list.destutter'_cons_neg List.destutter'_cons_neg

variable (R)

@[simp]
theorem destutter'_singleton : [b].destutter' R a = if R a b then [a, b] else [a] := by
  split_ifs with h <;> simp! [h]
  -- ⊢ destutter' R a [b] = [a, b]
                       -- 🎉 no goals
                       -- 🎉 no goals
#align list.destutter'_singleton List.destutter'_singleton

theorem destutter'_sublist (a) : l.destutter' R a <+ a :: l := by
  induction' l with b l hl generalizing a
  -- ⊢ destutter' R a [] <+ [a]
  · simp
    -- 🎉 no goals
  rw [destutter']
  -- ⊢ (if R a b then a :: destutter' R b l else destutter' R a l) <+ a :: b :: l
  split_ifs
  -- ⊢ a :: destutter' R b l <+ a :: b :: l
  · exact Sublist.cons₂ a (hl b)
    -- 🎉 no goals
  · exact (hl a).trans ((l.sublist_cons b).cons_cons a)
    -- 🎉 no goals
#align list.destutter'_sublist List.destutter'_sublist

theorem mem_destutter' (a) : a ∈ l.destutter' R a := by
  induction' l with b l hl
  -- ⊢ a ∈ destutter' R a []
  · simp
    -- 🎉 no goals
  rw [destutter']
  -- ⊢ a ∈ if R a b then a :: destutter' R b l else destutter' R a l
  split_ifs
  -- ⊢ a ∈ a :: destutter' R b l
  · simp
    -- 🎉 no goals
  · assumption
    -- 🎉 no goals
#align list.mem_destutter' List.mem_destutter'

theorem destutter'_is_chain : ∀ l : List α, ∀ {a b}, R a b → (l.destutter' R b).Chain R a
  | [], a, b, h => chain_singleton.mpr h
  | c :: l, a, b, h => by
    rw [destutter']
    -- ⊢ Chain R a (if R b c then b :: destutter' R c l else destutter' R b l)
    split_ifs with hbc
    -- ⊢ Chain R a (b :: destutter' R c l)
    · rw [chain_cons]
      -- ⊢ R a b ∧ Chain R b (destutter' R c l)
      exact ⟨h, destutter'_is_chain l hbc⟩
      -- 🎉 no goals
    · exact destutter'_is_chain l h
      -- 🎉 no goals
#align list.destutter'_is_chain List.destutter'_is_chain

theorem destutter'_is_chain' (a) : (l.destutter' R a).Chain' R := by
  induction' l with b l hl generalizing a
  -- ⊢ Chain' R (destutter' R a [])
  · simp
    -- 🎉 no goals
  rw [destutter']
  -- ⊢ Chain' R (if R a b then a :: destutter' R b l else destutter' R a l)
  split_ifs with h
  -- ⊢ Chain' R (a :: destutter' R b l)
  · exact destutter'_is_chain R l h
    -- 🎉 no goals
  · exact hl a
    -- 🎉 no goals
#align list.destutter'_is_chain' List.destutter'_is_chain'

theorem destutter'_of_chain (h : l.Chain R a) : l.destutter' R a = a :: l := by
  induction' l with b l hb generalizing a
  -- ⊢ destutter' R a [] = [a]
  · simp
    -- 🎉 no goals
  obtain ⟨h, hc⟩ := chain_cons.mp h
  -- ⊢ destutter' R a (b :: l) = a :: b :: l
  rw [l.destutter'_cons_pos h, hb hc]
  -- 🎉 no goals
#align list.destutter'_of_chain List.destutter'_of_chain

@[simp]
theorem destutter'_eq_self_iff (a) : l.destutter' R a = a :: l ↔ l.Chain R a :=
  ⟨fun h => by
    suffices Chain' R (a::l) by
      assumption
    rw [← h]
    -- ⊢ Chain' R (destutter' R a l)
    exact l.destutter'_is_chain' R a, destutter'_of_chain _ _⟩
    -- 🎉 no goals
#align list.destutter'_eq_self_iff List.destutter'_eq_self_iff

theorem destutter'_ne_nil : l.destutter' R a ≠ [] :=
  ne_nil_of_mem <| l.mem_destutter' R a
#align list.destutter'_ne_nil List.destutter'_ne_nil

@[simp]
theorem destutter_nil : ([] : List α).destutter R = [] :=
  rfl
#align list.destutter_nil List.destutter_nil

theorem destutter_cons' : (a :: l).destutter R = destutter' R a l :=
  rfl
#align list.destutter_cons' List.destutter_cons'

theorem destutter_cons_cons :
    (a :: b :: l).destutter R = if R a b then a :: destutter' R b l else destutter' R a l :=
  rfl
#align list.destutter_cons_cons List.destutter_cons_cons

@[simp]
theorem destutter_singleton : destutter R [a] = [a] :=
  rfl
#align list.destutter_singleton List.destutter_singleton

@[simp]
theorem destutter_pair : destutter R [a, b] = if R a b then [a, b] else [a] :=
  destutter_cons_cons _ R
#align list.destutter_pair List.destutter_pair

theorem destutter_sublist : ∀ l : List α, l.destutter R <+ l
  | [] => Sublist.slnil
  | h :: l => l.destutter'_sublist R h
#align list.destutter_sublist List.destutter_sublist

theorem destutter_is_chain' : ∀ l : List α, (l.destutter R).Chain' R
  | [] => List.chain'_nil
  | h :: l => l.destutter'_is_chain' R h
#align list.destutter_is_chain' List.destutter_is_chain'

theorem destutter_of_chain' : ∀ l : List α, l.Chain' R → l.destutter R = l
  | [], _ => rfl
  | _ :: l, h => l.destutter'_of_chain _ h
#align list.destutter_of_chain' List.destutter_of_chain'

@[simp]
theorem destutter_eq_self_iff : ∀ l : List α, l.destutter R = l ↔ l.Chain' R
  | [] => by simp
             -- 🎉 no goals
  | a :: l => l.destutter'_eq_self_iff R a
#align list.destutter_eq_self_iff List.destutter_eq_self_iff

theorem destutter_idem : (l.destutter R).destutter R = l.destutter R :=
  destutter_of_chain' R _ <| l.destutter_is_chain' R
#align list.destutter_idem List.destutter_idem

@[simp]
theorem destutter_eq_nil : ∀ {l : List α}, destutter R l = [] ↔ l = []
  | [] => Iff.rfl
  | _ :: l => ⟨fun h => absurd h <| l.destutter'_ne_nil R, fun h => nomatch h⟩
#align list.destutter_eq_nil List.destutter_eq_nil

end List
