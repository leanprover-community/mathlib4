/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.string.basic
! leanprover-community/mathlib commit d13b3a4a392ea7273dfa4727dbd1892e26cfd518
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.List.Lex
import Mathlib.Data.Char

/-!
# Strings

Supplementary theorems about the `String` type.
-/

namespace String

@[simp]
theorem Pos.byteIdx_zero : (0 : Pos).byteIdx = 0 :=
  rfl

@[simp]
theorem Pos.eq_iff {i₁ i₂ : Pos} : i₁ = i₂ ↔ i₁.byteIdx = i₂.byteIdx :=
  ⟨fun h ↦ h ▸ rfl, fun h ↦ show ⟨i₁.byteIdx⟩ = (⟨i₂.byteIdx⟩ : Pos) from h ▸ rfl⟩

@[simp]
theorem Pos.zero_add_char (c : Char) : (0 : Pos) + c = ⟨csize c⟩ :=
  show ⟨0 + csize c⟩ = (⟨csize c⟩ : Pos) by rw [Nat.zero_add]

@[simp]
theorem Pos.zero_add_string (s : String) : (0 : Pos) + s = ⟨s.utf8ByteSize⟩ :=
  show ⟨0 + s.utf8ByteSize⟩ = (⟨s.utf8ByteSize⟩ : Pos) by rw [Nat.zero_add]

/-- Induction on `String.utf8GetAux`. -/
def utf8GetAux.inductionOn.{u} {motive : List Char → Pos → Pos → Sort u}
    (s : List Char) (i p : Pos)
    (nil : ∀ i p, motive [] i p)
    (eq  : ∀ c cs i p, i = p → motive (c :: cs) i p)
    (ind : ∀ c cs i p, i ≠ p → motive cs ⟨i.byteIdx + csize c⟩ p → motive (c :: cs) i p) :
    motive s i p :=
  match s with
  | [] => nil i p
  | c::cs =>
    if h : i = p then
      eq c cs i p h
    else ind c cs i p h (inductionOn cs ⟨i.byteIdx + csize c⟩ p nil eq ind)

open private utf8GetAux from Init.Data.String.Basic

private lemma utf8GetAux.add_right_cancel (s : List Char) (i p n : ℕ) :
    utf8GetAux s ⟨i + n⟩ ⟨p + n⟩ = utf8GetAux s ⟨i⟩ ⟨p⟩ := by
  apply inductionOn s ⟨i⟩ ⟨p⟩ (motive := fun s i p ↦
    utf8GetAux s ⟨i.byteIdx + n⟩ ⟨p.byteIdx + n⟩ = utf8GetAux s i p) <;>
  simp [utf8GetAux]
  · intro c cs ⟨i⟩ ⟨p⟩ h
    simp at h
    subst i
    simp
  · intro c cs ⟨i⟩ ⟨p⟩ h ih
    simp at h
    simp [h]
    show utf8GetAux cs ⟨i + n + csize c⟩ ⟨p + n⟩ = utf8GetAux cs ⟨i + csize c⟩ ⟨p⟩
    rw [Nat.add_right_comm]
    exact ih

lemma get.cons_add_csize (c : Char) (cs : List Char) (i : ℕ) :
    get ⟨c :: cs⟩ ⟨i + csize c⟩ = get ⟨cs⟩ ⟨i⟩ := by
  have : 0 ≠ i + csize c := Nat.ne_of_lt (Nat.add_pos_right i (csize_pos c))
  simp [get, utf8GetAux, this]
  rw [← Pos.zero_add_char]
  apply utf8GetAux.add_right_cancel

lemma Iterator.hasNext.cons_add_csize (c : Char) (cs : List Char) (i : ℕ) :
    hasNext ⟨⟨c :: cs⟩, ⟨i + csize c⟩⟩ = hasNext ⟨⟨cs⟩, ⟨i⟩⟩ := by
  simp [hasNext, endPos, utf8ByteSize, utf8ByteSize.go]

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

lemma ltb.cons_add_csize (c : Char) (cs₁ cs₂ : List Char) (i₁ i₂ : ℕ) :
    ltb ⟨⟨c :: cs₁⟩, ⟨i₁ + csize c⟩⟩ ⟨⟨c :: cs₂⟩, ⟨i₂ + csize c⟩⟩ =
    ltb ⟨⟨cs₁⟩, ⟨i₁⟩⟩ ⟨⟨cs₂⟩, ⟨i₂⟩⟩ := by
  apply inductionOn ⟨⟨cs₁⟩, ⟨i₁⟩⟩ ⟨⟨cs₂⟩, ⟨i₂⟩⟩ (motive := fun ⟨⟨cs₁⟩, ⟨i₁⟩⟩ ⟨⟨cs₂⟩, ⟨i₂⟩⟩ ↦
    ltb ⟨⟨c :: cs₁⟩, ⟨i₁ + csize c⟩⟩ ⟨⟨c :: cs₂⟩, ⟨i₂ + csize c⟩⟩ =
    ltb ⟨⟨cs₁⟩, ⟨i₁⟩⟩ ⟨⟨cs₂⟩, ⟨i₂⟩⟩) <;> simp <;>
  intro ⟨cs₁⟩ ⟨cs₂⟩ ⟨i₁⟩ ⟨i₂⟩ <;>
  intros <;>
  (conv => lhs; rw [ltb]) <;> (conv => rhs; rw [ltb]) <;>
  simp [Iterator.hasNext.cons_add_csize, *]
  · rename_i h₂ h₁ heq ih
    simp [Iterator.curr, Iterator.next, next, Iterator.hasNext.cons_add_csize,
          get.cons_add_csize, *] at *
    show ltb ⟨⟨c :: cs₁⟩, ⟨i₁ + csize c + csize (get ⟨cs₂⟩ ⟨i₂⟩)⟩⟩
             ⟨⟨c :: cs₂⟩, ⟨i₂ + csize c + csize (get ⟨cs₂⟩ ⟨i₂⟩)⟩⟩ =
         ltb ⟨⟨cs₁⟩, ⟨i₁ + csize (get ⟨cs₂⟩ ⟨i₂⟩)⟩⟩ ⟨⟨cs₂⟩, ⟨i₂ + csize (get ⟨cs₂⟩ ⟨i₂⟩)⟩⟩
    repeat rw [Nat.add_right_comm _ (csize c)]
    exact ih
  · rename_i h₂ h₁ hne
    simp [Iterator.curr, Iterator.hasNext.cons_add_csize, get.cons_add_csize, *] at *

@[simp]
theorem lt_iff_toList_lt : ∀ {s₁ s₂ : String}, s₁ < s₂ ↔ s₁.toList < s₂.toList
| ⟨s₁⟩, ⟨s₂⟩ => show ltb ⟨⟨s₁⟩, 0⟩ ⟨⟨s₂⟩, 0⟩ ↔ s₁ < s₂ by
  induction s₁ generalizing s₂ <;> cases s₂
  · simp
  · rename_i c₂ cs₂; apply iff_of_true
    · rw [ltb]; simp; apply ne_false_of_eq_true; apply decide_eq_true
      simp [endPos, utf8ByteSize, utf8ByteSize.go, csize_pos]
    · apply List.nil_lt_cons
  · rename_i c₁ cs₁ ih; apply iff_of_false
    · rw [ltb]; simp
    · apply not_lt_of_lt; apply List.nil_lt_cons
  · rename_i c₁ cs₁ ih c₂ cs₂; rw [ltb]
    simp [Iterator.hasNext, Iterator.curr, Iterator.next, next, endPos, utf8ByteSize,
          utf8ByteSize.go, csize_pos]; rw [decide_eq_true_iff]
    show (if c₁ = c₂ then
            ltb ⟨⟨c₁ :: cs₁⟩, ⟨csize c₁⟩⟩ ⟨⟨c₂ :: cs₂⟩, ⟨csize c₂⟩⟩ = true
          else c₁ < c₂) ↔ c₁ :: cs₁ < c₂ :: cs₂
    split_ifs with h
    · subst c₂
      suffices ltb ⟨⟨c₁ :: cs₁⟩, ⟨csize c₁⟩⟩ ⟨⟨c₁ :: cs₂⟩, ⟨csize c₁⟩⟩ = ltb ⟨⟨cs₁⟩, 0⟩ ⟨⟨cs₂⟩, 0⟩
        by rw [this]; exact (ih cs₂).trans List.Lex.cons_iff.symm
      rw [← Pos.zero_add_char]
      apply ltb.cons_add_csize
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

theorem nil_asString_eq_empty : [].asString = "" :=
  rfl
#align string.nil_as_string_eq_empty String.nil_asString_eq_empty

@[simp]
theorem toList_empty : "".toList = [] :=
  rfl
#align string.to_list_empty String.toList_empty

theorem asString_inv_toList (s : String) : s.toList.asString = s :=
  rfl
#align string.as_string_inv_to_list String.asString_inv_toList

@[simp]
theorem toList_singleton (c : Char) : (String.singleton c).toList = [c] :=
  rfl
#align string.to_list_singleton String.toList_singleton

theorem toList_nonempty : ∀ {s : String}, s ≠ "" → s.toList = s.head :: (s.popn 1).toList
| ⟨s⟩, h => by
  cases s
  · simp only [toList] at h
  · rename_i c cs
    simp only [toList, List.cons.injEq]
    constructor <;>
    rfl
#align string.to_list_nonempty String.toList_nonempty

@[simp]
theorem head_empty : "".data.head! = default :=
  rfl
#align string.head_empty String.head_empty

@[simp]
theorem popn_empty {n : ℕ} : "".popn n = "" := by
  simp [popn]
#align string.popn_empty String.popn_empty

instance : LinearOrder String where
  le_refl a := le_iff_toList_le.mpr le_rfl
  le_trans a b c := by
    simp only [le_iff_toList_le]
    apply le_trans
  lt_iff_le_not_le a b := by
    simp only [le_iff_toList_le, lt_iff_toList_lt, lt_iff_le_not_le]
  le_antisymm a b := by
    simp only [le_iff_toList_le, ← toList_inj]
    apply le_antisymm
  le_total a b := by
    simp only [le_iff_toList_le]
    apply le_total
  decidable_le := String.decidableLE
  compare_eq_compareOfLessAndEq a b := by
    simp [compare, compareOfLessAndEq, toList, instLTString, List.instLTList, List.LT']
    split_ifs <;>
    simp [List.lt_iff_lex_lt] at * <;>
    contradiction

end String

open String

theorem List.toList_inv_asString (l : List Char) : l.asString.toList = l :=
  rfl
#align list.to_list_inv_as_string List.toList_inv_asString

@[simp]
theorem List.length_asString (l : List Char) : l.asString.length = l.length :=
  rfl
#align list.length_as_string List.length_asString

@[simp]
theorem List.asString_inj {l l' : List Char} : l.asString = l'.asString ↔ l = l' :=
  ⟨fun h ↦ by rw [← toList_inv_asString l, ← toList_inv_asString l', toList_inj, h],
   fun h ↦ h ▸ rfl⟩
#align list.as_string_inj List.asString_inj

@[simp]
theorem String.length_toList (s : String) : s.toList.length = s.length := by
  rw [← String.asString_inv_toList s, List.toList_inv_asString, List.length_asString]
#align string.length_to_list String.length_toList

theorem List.asString_eq {l : List Char} {s : String} : l.asString = s ↔ l = s.toList := by
  rw [← asString_inv_toList s, asString_inj, asString_inv_toList s]
#align list.as_string_eq List.asString_eq
