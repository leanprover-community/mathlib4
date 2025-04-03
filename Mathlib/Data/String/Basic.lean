/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.List.Lex
import Mathlib.Data.Char
import Mathlib.Tactic.AdaptationNote
import Mathlib.Algebra.Order.Group.Nat

#align_import data.string.basic from "leanprover-community/mathlib"@"d13b3a4a392ea7273dfa4727dbd1892e26cfd518"

/-!
# Strings

Supplementary theorems about the `String` type.
-/

namespace String

/-- `<` on string iterators. This coincides with `<` on strings as lists. -/
def ltb (s₁ s₂ : Iterator) : Bool :=
  if s₂.hasNext then
    if s₁.hasNext then
      if s₁.curr = s₂.curr then
        ltb s₁.next s₂.next
      else s₁.curr < s₂.curr
    else true
  else false
#align string.ltb String.ltb

instance LT' : LT String :=
  ⟨fun s₁ s₂ ↦ ltb s₁.iter s₂.iter⟩
#align string.has_lt' String.LT'

instance decidableLT : @DecidableRel String (· < ·) := by
  simp only [LT']
  infer_instance -- short-circuit type class inference
#align string.decidable_lt String.decidableLT

/-- Induction on `String.ltb`. -/
def ltb.inductionOn.{u} {motive : Iterator → Iterator → Sort u} (it₁ it₂ : Iterator)
    (ind : ∀ s₁ s₂ i₁ i₂, Iterator.hasNext ⟨s₂, i₂⟩ → Iterator.hasNext ⟨s₁, i₁⟩ →
      get s₁ i₁ = get s₂ i₂ → motive (Iterator.next ⟨s₁, i₁⟩) (Iterator.next ⟨s₂, i₂⟩) →
      motive ⟨s₁, i₁⟩ ⟨s₂, i₂⟩)
    (eq : ∀ s₁ s₂ i₁ i₂, Iterator.hasNext ⟨s₂, i₂⟩ → Iterator.hasNext ⟨s₁, i₁⟩ →
      ¬ get s₁ i₁ = get s₂ i₂ → motive ⟨s₁, i₁⟩ ⟨s₂, i₂⟩)
    (base₁ : ∀ s₁ s₂ i₁ i₂, Iterator.hasNext ⟨s₂, i₂⟩ → ¬ Iterator.hasNext ⟨s₁, i₁⟩ →
      motive ⟨s₁, i₁⟩ ⟨s₂, i₂⟩)
    (base₂ : ∀ s₁ s₂ i₁ i₂, ¬ Iterator.hasNext ⟨s₂, i₂⟩ → motive ⟨s₁, i₁⟩ ⟨s₂, i₂⟩) :
    motive it₁ it₂ :=
  if h₂ : it₂.hasNext then
    if h₁ : it₁.hasNext then
      if heq : it₁.curr = it₂.curr then
        ind it₁.s it₂.s it₁.i it₂.i h₂ h₁ heq (inductionOn it₁.next it₂.next ind eq base₁ base₂)
      else eq it₁.s it₂.s it₁.i it₂.i h₂ h₁ heq
    else base₁ it₁.s it₂.s it₁.i it₂.i h₂ h₁
  else base₂ it₁.s it₂.s it₁.i it₂.i h₂

theorem ltb_cons_addChar (c : Char) (cs₁ cs₂ : List Char) (i₁ i₂ : Pos) :
    ltb ⟨⟨c :: cs₁⟩, i₁ + c⟩ ⟨⟨c :: cs₂⟩, i₂ + c⟩ = ltb ⟨⟨cs₁⟩, i₁⟩ ⟨⟨cs₂⟩, i₂⟩ := by
  apply ltb.inductionOn ⟨⟨cs₁⟩, i₁⟩ ⟨⟨cs₂⟩, i₂⟩ (motive := fun ⟨⟨cs₁⟩, i₁⟩ ⟨⟨cs₂⟩, i₂⟩ ↦
    ltb ⟨⟨c :: cs₁⟩, i₁ + c⟩ ⟨⟨c :: cs₂⟩, i₂ + c⟩ =
    ltb ⟨⟨cs₁⟩, i₁⟩ ⟨⟨cs₂⟩, i₂⟩) <;> simp only <;>
  intro ⟨cs₁⟩ ⟨cs₂⟩ i₁ i₂ <;>
  intros <;>
  (conv => lhs; unfold ltb) <;> (conv => rhs; unfold ltb) <;>
  simp only [Iterator.hasNext_cons_addChar, ite_false, ite_true, *]
  · rename_i h₂ h₁ heq ih
    simp only [Iterator.next, next, heq, Iterator.curr, get_cons_addChar, ite_true] at ih ⊢
    repeat rw [Pos.addChar_right_comm _ c]
    exact ih
  · rename_i h₂ h₁ hne
    simp [Iterator.curr, get_cons_addChar, hne]

@[simp]
theorem lt_iff_toList_lt : ∀ {s₁ s₂ : String}, s₁ < s₂ ↔ s₁.toList < s₂.toList
  | ⟨s₁⟩, ⟨s₂⟩ => show ltb ⟨⟨s₁⟩, 0⟩ ⟨⟨s₂⟩, 0⟩ ↔ s₁ < s₂ by
    induction s₁ generalizing s₂ <;> cases s₂
    · unfold ltb; decide
    · rename_i c₂ cs₂; apply iff_of_true
      · unfold ltb
        #adaptation_note /-- v4.7.0-rc1 exclude reduceMk from simp -/
        simp [-reduceMk, Iterator.hasNext, Char.utf8Size_pos]
      · apply List.nil_lt_cons
    · rename_i c₁ cs₁ ih; apply iff_of_false
      · unfold ltb
        #adaptation_note /-- v4.7.0-rc1 exclude reduceMk from simp -/
        simp [-reduceMk, Iterator.hasNext]
      · apply not_lt_of_lt; apply List.nil_lt_cons
    · rename_i c₁ cs₁ ih c₂ cs₂; unfold ltb
      simp only [Iterator.hasNext, Pos.byteIdx_zero, endPos, utf8ByteSize, utf8ByteSize.go,
        add_pos_iff, Char.utf8Size_pos, or_true, decide_eq_true_eq, ↓reduceIte, Iterator.curr, get,
        utf8GetAux, Iterator.next, next, Bool.ite_eq_true_distrib]
      split_ifs with h
      · subst c₂
        suffices ltb ⟨⟨c₁ :: cs₁⟩, (0 : Pos) + c₁⟩ ⟨⟨c₁ :: cs₂⟩, (0 : Pos) + c₁⟩ =
          ltb ⟨⟨cs₁⟩, 0⟩ ⟨⟨cs₂⟩, 0⟩ by rw [this]; exact (ih cs₂).trans List.Lex.cons_iff.symm
        apply ltb_cons_addChar
      · refine ⟨List.Lex.rel, fun e ↦ ?_⟩
        cases e <;> rename_i h'
        · contradiction
        · assumption
#align string.lt_iff_to_list_lt String.lt_iff_toList_lt

instance LE : LE String :=
  ⟨fun s₁ s₂ ↦ ¬s₂ < s₁⟩
#align string.has_le String.LE

instance decidableLE : @DecidableRel String (· ≤ ·) := by
  simp only [LE]
  infer_instance -- short-circuit type class inference
#align string.decidable_le String.decidableLE

@[simp]
theorem le_iff_toList_le {s₁ s₂ : String} : s₁ ≤ s₂ ↔ s₁.toList ≤ s₂.toList :=
  (not_congr lt_iff_toList_lt).trans not_lt
#align string.le_iff_to_list_le String.le_iff_toList_le

theorem toList_inj {s₁ s₂ : String} : s₁.toList = s₂.toList ↔ s₁ = s₂ :=
  ⟨congr_arg mk, congr_arg toList⟩
#align string.to_list_inj String.toList_inj

theorem asString_nil : [].asString = "" :=
  rfl
#align string.nil_as_string_eq_empty String.asString_nil

@[deprecated (since := "2024-06-04")] alias nil_asString_eq_empty := asString_nil

@[simp]
theorem toList_empty : "".toList = [] :=
  rfl
#align string.to_list_empty String.toList_empty

theorem asString_toList (s : String) : s.toList.asString = s :=
  rfl
#align string.as_string_inv_to_list String.asString_toList

@[deprecated (since := "2024-06-04")] alias asString_inv_toList := asString_toList

#align string.to_list_singleton String.data_singleton

theorem toList_nonempty : ∀ {s : String}, s ≠ "" → s.toList = s.head :: (s.drop 1).toList
  | ⟨s⟩, h => by
    cases s with
    | nil => simp at h
    | cons c cs =>
      simp only [toList, data_drop, List.drop_succ_cons, List.drop_zero, List.cons.injEq, and_true]
      rfl
#align string.to_list_nonempty String.toList_nonempty

@[simp]
theorem head_empty : "".data.head! = default :=
  rfl
#align string.head_empty String.head_empty

#align string.popn_empty String.drop_empty

instance : LinearOrder String where
  le_refl a := le_iff_toList_le.mpr le_rfl
  le_trans a b c := by
    simp only [le_iff_toList_le]
    apply le_trans
  lt_iff_le_not_le a b := by
    simp only [lt_iff_toList_lt, le_iff_toList_le, lt_iff_le_not_le]
  le_antisymm a b := by
    simp only [le_iff_toList_le, ← toList_inj]
    apply le_antisymm
  le_total a b := by
    simp only [le_iff_toList_le]
    apply le_total
  decidableLE := String.decidableLE
  compare_eq_compareOfLessAndEq a b := by
    simp only [compare, compareOfLessAndEq, instLT, List.instLT, lt_iff_toList_lt, toList]
    split_ifs <;>
    simp only [List.lt_iff_lex_lt] at * <;>
    contradiction

end String

open String

namespace List

theorem toList_asString (l : List Char) : l.asString.toList = l :=
  rfl
#align list.to_list_inv_as_string List.toList_asString

@[deprecated (since := "2024-06-04")] alias toList_inv_asString := toList_asString

@[simp]
theorem length_asString (l : List Char) : l.asString.length = l.length :=
  rfl
#align list.length_as_string List.length_asString

@[simp]
theorem asString_inj {l l' : List Char} : l.asString = l'.asString ↔ l = l' :=
  ⟨fun h ↦ by rw [← toList_asString l, ← toList_asString l', toList_inj, h],
   fun h ↦ h ▸ rfl⟩
#align list.as_string_inj List.asString_inj

theorem asString_eq {l : List Char} {s : String} : l.asString = s ↔ l = s.toList := by
  rw [← asString_toList s, asString_inj, asString_toList s]
#align list.as_string_eq List.asString_eq

end List

@[simp]
theorem String.length_data (s : String) : s.data.length = s.length :=
  rfl
#align string.length_to_list String.length_data
