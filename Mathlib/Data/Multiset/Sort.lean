/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.List.Sort
import Mathlib.Data.Multiset.Range
import Mathlib.Util.Qq

/-!
# Construct a sorted list from a multiset.
-/

variable {α β : Type*}

namespace Multiset

open List

section sort

variable (r : α → α → Prop) [DecidableRel r] [IsTrans α r] [IsAntisymm α r] [IsTotal α r]
variable (r' : β → β → Prop) [DecidableRel r'] [IsTrans β r'] [IsAntisymm β r'] [IsTotal β r']

/-- `sort s` constructs a sorted list from the multiset `s`.
  (Uses merge sort algorithm.) -/
def sort (s : Multiset α) : List α :=
  Quot.liftOn s (mergeSort · (r · ·)) fun _ _ h =>
    eq_of_perm_of_sorted ((mergeSort_perm _ _).trans <| h.trans (mergeSort_perm _ _).symm)
      (sorted_mergeSort IsTrans.trans
        (fun a b => by simpa using IsTotal.total a b) _)
      (sorted_mergeSort IsTrans.trans
        (fun a b => by simpa using IsTotal.total a b) _)

@[simp]
theorem coe_sort (l : List α) : sort r l = mergeSort l (r · ·) :=
  rfl

@[simp]
theorem sort_sorted (s : Multiset α) : Sorted r (sort r s) :=
  Quot.inductionOn s (sorted_mergeSort' _)

@[simp]
theorem sort_eq (s : Multiset α) : ↑(sort r s) = s :=
  Quot.inductionOn s fun _ => Quot.sound <| mergeSort_perm _ _

@[simp]
theorem mem_sort {s : Multiset α} {a : α} : a ∈ sort r s ↔ a ∈ s := by rw [← mem_coe, sort_eq]

@[simp]
theorem length_sort {s : Multiset α} : (sort r s).length = card s :=
  Quot.inductionOn s <| length_mergeSort

@[simp]
theorem sort_zero : sort r 0 = [] :=
  List.mergeSort_nil

@[simp]
theorem sort_singleton (a : α) : sort r {a} = [a] :=
  List.mergeSort_singleton a

theorem map_sort (f : α → β) (s : Multiset α)
    (hs : ∀ a ∈ s, ∀ b ∈ s, r a b ↔ r' (f a) (f b)) :
    (s.sort r).map f = (s.map f).sort r' := by
  revert s
  exact Quot.ind fun l h => map_mergeSort (l := l) (by simpa using h)

theorem sort_cons (a : α) (s : Multiset α) :
    (∀ b ∈ s, r a b) → sort r (a ::ₘ s) = a :: sort r s := by
  refine Quot.inductionOn s fun l => ?_
  simpa [mergeSort_eq_insertionSort] using insertionSort_cons r (a := a) (l := l)

@[simp]
theorem sort_range (n : ℕ) : sort (· ≤ ·) (range n) = List.range n :=
  List.mergeSort_eq_self _ (sorted_le_range n)

end sort

open Qq in
universe u in
unsafe instance {α : Type u} [Lean.ToLevel.{u}] [Lean.ToExpr α] :
    Lean.ToExpr (Multiset α) :=
  haveI u' := Lean.toLevel.{u}
  haveI α' : Q(Type u') := Lean.toTypeExpr α
  { toTypeExpr := q(Multiset $α')
    toExpr s := show Q(Multiset $α') from
      if Multiset.card s = 0 then
        q(0)
      else
        mkSetLiteralQ (α := q($α')) q(Multiset $α') (s.unquot.map Lean.toExpr)}

-- TODO: use a sort order if available, gh-18166
unsafe instance [Repr α] : Repr (Multiset α) where
  reprPrec s _ :=
    if Multiset.card s = 0 then
      "0"
    else
      Std.Format.bracket "{" (Std.Format.joinSep (s.unquot.map repr) ("," ++ Std.Format.line)) "}"

end Multiset
