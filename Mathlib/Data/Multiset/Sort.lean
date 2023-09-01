/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.List.Sort
import Mathlib.Data.Multiset.Basic

#align_import data.multiset.sort from "leanprover-community/mathlib"@"008205aa645b3f194c1da47025c5f110c8406eab"

/-!
# Construct a sorted list from a multiset.
-/


namespace Multiset

open List

variable {α : Type*}

section sort

variable (r : α → α → Prop) [DecidableRel r] [IsTrans α r] [IsAntisymm α r] [IsTotal α r]

/-- `sort s` constructs a sorted list from the multiset `s`.
  (Uses merge sort algorithm.) -/
def sort (s : Multiset α) : List α :=
  Quot.liftOn s (mergeSort r) fun _ _ h =>
    eq_of_perm_of_sorted ((perm_mergeSort _ _).trans <| h.trans (perm_mergeSort _ _).symm)
      (sorted_mergeSort r _) (sorted_mergeSort r _)
#align multiset.sort Multiset.sort

@[simp]
theorem coe_sort (l : List α) : sort r l = mergeSort r l :=
  rfl
#align multiset.coe_sort Multiset.coe_sort

@[simp]
theorem sort_sorted (s : Multiset α) : Sorted r (sort r s) :=
  Quot.inductionOn s fun _l => sorted_mergeSort r _
#align multiset.sort_sorted Multiset.sort_sorted

@[simp]
theorem sort_eq (s : Multiset α) : ↑(sort r s) = s :=
  Quot.inductionOn s fun _ => Quot.sound <| perm_mergeSort _ _
#align multiset.sort_eq Multiset.sort_eq

@[simp]
theorem mem_sort {s : Multiset α} {a : α} : a ∈ sort r s ↔ a ∈ s := by rw [← mem_coe, sort_eq]
#align multiset.mem_sort Multiset.mem_sort

@[simp]
theorem length_sort {s : Multiset α} : (sort r s).length = card s :=
  Quot.inductionOn s <| length_mergeSort _
#align multiset.length_sort Multiset.length_sort

@[simp]
theorem sort_zero : sort r 0 = [] :=
  List.mergeSort_nil r
#align multiset.sort_zero Multiset.sort_zero

@[simp]
theorem sort_singleton (a : α) : sort r {a} = [a] :=
  List.mergeSort_singleton r a
#align multiset.sort_singleton Multiset.sort_singleton

end sort

-- TODO: use a sort order if available, gh-18166
unsafe instance [Repr α] : Repr (Multiset α) where
  reprPrec s _ :=
    if Multiset.card s = 0 then
      "0"
    else
      Std.Format.bracket "{" (Std.Format.joinSep (s.unquot.map repr) ("," ++ Std.Format.line)) "}"

end Multiset
