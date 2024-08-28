/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.List.Sort
import Mathlib.Data.Multiset.Basic

/-!
# Construct a sorted list from a multiset.
-/


namespace Multiset

open List

variable {α β : Type*}

section sort

variable (r : α → α → Prop) [DecidableRel r] [IsTrans α r] [IsAntisymm α r] [IsTotal α r]
variable (r' : β → β → Prop) [DecidableRel r'] [IsTrans β r'] [IsAntisymm β r'] [IsTotal β r']

/-- `sort s` constructs a sorted list from the multiset `s`.
  (Uses merge sort algorithm.) -/
def sort (s : Multiset α) : List α :=
  Quot.liftOn s (mergeSort r) fun _ _ h =>
    eq_of_perm_of_sorted ((perm_mergeSort _ _).trans <| h.trans (perm_mergeSort _ _).symm)
      (sorted_mergeSort r _) (sorted_mergeSort r _)

@[simp]
theorem coe_sort (l : List α) : sort r l = mergeSort r l :=
  rfl

@[simp]
theorem sort_sorted (s : Multiset α) : Sorted r (sort r s) :=
  Quot.inductionOn s fun _l => sorted_mergeSort r _

@[simp]
theorem sort_eq (s : Multiset α) : ↑(sort r s) = s :=
  Quot.inductionOn s fun _ => Quot.sound <| perm_mergeSort _ _

@[simp]
theorem mem_sort {s : Multiset α} {a : α} : a ∈ sort r s ↔ a ∈ s := by rw [← mem_coe, sort_eq]

@[simp]
theorem length_sort {s : Multiset α} : (sort r s).length = card s :=
  Quot.inductionOn s <| length_mergeSort _

@[simp]
theorem sort_zero : sort r 0 = [] :=
  List.mergeSort_nil r

@[simp]
theorem sort_singleton (a : α) : sort r {a} = [a] :=
  List.mergeSort_singleton r a

theorem map_sort (f : α → β) (s : Multiset α)
    (hs : ∀ a ∈ s, ∀ b ∈ s, r a b ↔ r' (f a) (f b)) :
    (s.sort r).map f = (s.map f).sort r' := by
  revert s
  exact Quot.ind fun _ => List.map_mergeSort _ _ _ _

end sort

-- TODO: use a sort order if available, gh-18166
unsafe instance [Repr α] : Repr (Multiset α) where
  reprPrec s _ :=
    if Multiset.card s = 0 then
      "0"
    else
      Std.Format.bracket "{" (Std.Format.joinSep (s.unquot.map repr) ("," ++ Std.Format.line)) "}"

end Multiset
