/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.string.basic
! leanprover-community/mathlib commit 8a275d92e9f9f3069871cbdf0ddd54b88c17e144
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.List.Lex
import Mathlib.Data.Char
import Std.Tactic.RCases
import Mathlib.Tactic.LibrarySearch

/-!
# Strings

Supplementary theorems about the `String` type.
-/


namespace String

/-- `<` on string iterators. This coincides with `<` on strings as lists. -/
def ltb (s₁ s₂ : Iterator) : Bool :=
  if s₂.hasNext then
    if s₁.hasNext then
      if s₁.curr = s₂.curr then ltb s₁.next s₂.next
      else s₁.curr < s₂.curr
    else true
  else false
#align string.ltb String.ltb

instance lt' : LT String :=
  ⟨fun s₁ s₂ => ltb s₁.mkIterator s₂.mkIterator⟩
#align string.has_lt' String.lt'

instance decidable_lt : @DecidableRel String (· < ·) := by
  simp only [lt']
  infer_instance  -- short-circuit type class inference
#align string.decidable_lt String.decidable_lt

-- TODO move this to the appropriate place
theorem zero_lt_utf8Size (c : Char) : 0 < c.utf8Size.toNat := by
  simp only [Char.utf8Size]
  split_ifs <;> simp

-- TODO move this to the appropriate place
theorem zero_lt_utf8ByteSize_cons : 0 < utf8ByteSize ⟨hd :: tl⟩ := by
  simp only [utf8ByteSize, utf8ByteSize.go, csize]
  apply lt_of_lt_of_le
  · exact zero_lt_utf8Size hd
  · apply Nat.le_add_left

-- TODO move this to the appropriate place
@[simp]
theorem Iterator.hasNext_mkIterator_cons : (mkIterator ⟨hd :: tl⟩).hasNext = true := by
  simp only [mkIterator, Iterator.hasNext, endPos, show (0 : Pos).byteIdx = 0 by rfl,
    zero_lt_utf8ByteSize_cons, decide_True]

@[simp]
theorem String.extract_zero_endPos : String.extract s 0 (endPos s) = s := by
  have s_eq_s_data : s = ⟨s.data⟩ := rfl
  rw [s_eq_s_data]
  induction s.data with
  | nil => rfl
  | cons head tail tail_ih =>
    simp only [extract, endPos]
    have : ¬ (0 : Pos).byteIdx ≥ utf8ByteSize { data := head :: tail } :=
      not_le.2 zero_lt_utf8ByteSize_cons
    simp only [this, ite_false, extract.go₁, extract.go₂, ite_true]
    have : (0 : Pos) ≠ { byteIdx := utf8ByteSize { data := head :: tail } } :=
      fun x ↦ this (of_eq <| congrArg Pos.byteIdx x)
    simp [this]
    simp [extract, endPos] at tail_ih
    by_cases h : utf8ByteSize { data := tail } ≤ (0 : Pos).byteIdx
    · simp [h] at tail_ih
      have : tail = [] := symm <| congrArg data tail_ih
      rw [this]
      simp only [extract.go₂]
    · simp [h] at tail_ih


theorem adsiofuo {n : ℕ} (h : n ≤ 0) : n = 0 := Nat.eq_zero_of_le_zero h

@[simp]
theorem String.extract_empty : String.extract ⟨[]⟩ p₁ p₂ = ⟨[]⟩ := by
  simp [extract, extract.go₁]

@[simp]
theorem Iterator.mkIterator_remainingToString (s : String) :
    (mkIterator s).remainingToString = s := by
  simp [Iterator.remainingToString, mkIterator]

theorem Iterator.hasNext_iff_remainingToString_not_empty (i : Iterator) :
    i.hasNext ↔ i.remainingToString.toList ≠ [] := by
  apply Iff.intro
  · intro h
    rw [hasNext] at h
    simp only [decide_eq_true_eq] at h
    rw [remainingToString]
    simp only

theorem Iterator.curr_eq_hd_remainingToString (i : Iterator) :
    i.curr = i.remainingToString.toList.headD default := sorry

theorem Iterator.hasNextRec {p : (i : Iterator) → i.hasNext → Prop}
    (hp : ∀ i hi' hi, p i.next hi' → p i hi) : ∀ i (hi : i.hasNext), p i hi := sorry

theorem Iterator.next_remainingToString (i : Iterator) :
    (Iterator.next i).remainingToString.toList = i.remainingToString.toList.tail := sorry

namespace List.Lex

theorem cons_iff_of_ne {r : α → α → Prop} [IsIrrefl α r] {a₁ a₂ l₁ l₂} (h : a₁ ≠ a₂):
    List.Lex r (a₁ :: l₁) (a₂ :: l₂) ↔ r a₁ a₂ :=
  ⟨fun h => by
    cases h
    · exfalso; apply h; rfl
    · assumption,
   List.Lex.rel⟩

end List.Lex

-- TODO This proof probably has to be completely redone
@[simp]
theorem lt_iff_toList_lt : ∀ {s₁ s₂ : String}, s₁ < s₂ ↔ s₁.toList < s₂.toList := by
  suffices ∀ i₁ i₂, ltb i₁ i₂ ↔ i₁.remainingToString.toList < i₂.remainingToString.toList by
    intro s₁ s₂
    have := this (mkIterator s₁) (mkIterator s₂)
    simp only [Iterator.mkIterator_remainingToString] at this
    exact this
  intro i₁ i₂
  change _ ↔ List.Lex _ _ _
  by_cases h₂ : i₂.hasNext
  · revert i₁
    apply Iterator.hasNextRec ?_ i₂ h₂
    intro i₂ _ hi₂ IH i₁
    simp only [hi₂, ite_true]
    rw [ltb]
    split_ifs with h₁ hc
      <;> rw [Iterator.hasNext_iff_remainingToString_not_empty] at h₁ hi₂
      <;> rcases List.exists_cons_of_ne_nil hi₂ with ⟨_, _, hi₂⟩
    · rw [IH]
      rcases List.exists_cons_of_ne_nil h₁ with ⟨_, _, hi₁⟩
      simp only [Iterator.curr_eq_hd_remainingToString, hi₁, List.headD_cons, hi₂] at hc
      simp [hi₁, hi₂, hc, List.Lex.cons_iff, Iterator.next_remainingToString]
    · rcases List.exists_cons_of_ne_nil h₁ with ⟨_, _, hi₁⟩
      simp [Iterator.curr_eq_hd_remainingToString, hi₂, hi₁] at *
      apply (List.Lex.cons_iff_of_ne hc).symm
    · simp only [of_not_not h₁, hi₂, true_iff, List.Lex.nil]
  · rw [ltb]
    simp only [h₂, if_false, false_iff]
    by_cases h₁ : i₁.hasNext <;> rw [Iterator.hasNext_iff_remainingToString_not_empty] at h₁ h₂
    · simp [of_not_not h₂]
    · simp [of_not_not h₁, of_not_not h₂]

instance le : LE String :=
  ⟨fun s₁ s₂ => ¬s₂ < s₁⟩
#align string.has_le String.le

instance decidableLe : @DecidableRel String (· ≤ ·) := by
  simp only [le]
  infer_instance  -- short-circuit type class inference
#align string.decidable_le String.decidableLe

@[simp]
theorem le_iff_toList_le {s₁ s₂ : String} : s₁ ≤ s₂ ↔ s₁.toList ≤ s₂.toList :=
  (not_congr lt_iff_toList_lt).trans not_lt
#align string.le_iff_to_list_le String.le_iff_toList_le

theorem toList_inj : ∀ {s₁ s₂}, toList s₁ = toList s₂ ↔ s₁ = s₂
  | ⟨_⟩, _ => ⟨congr_arg _, congr_arg _⟩
#align string.to_list_inj String.toList_inj

theorem nil_asString_eq_empty : [].asString = "" :=
  rfl
#align string.nil_as_string_eq_empty String.nil_asString_eq_empty

@[simp]
theorem toList_empty : "".toList = [] :=
  rfl
#align string.to_list_empty String.toList_empty

theorem asString_inv_toList (s : String) : s.toList.asString = s := by
  cases s
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
    · simp only [toList, List.cons.injEq]
      constructor
      · rfl
      · rfl
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
  lt := (· < ·)
  le := (· ≤ ·)
  decidable_lt := by infer_instance
  decidable_le := String.decidableLe
  decidable_eq := by infer_instance
  le_refl a := le_iff_toList_le.2 le_rfl
  le_trans a b c := by
    simp only [le_iff_toList_le]
    exact fun h₁ h₂ => h₁.trans h₂
  le_total a b := by
    simp only [le_iff_toList_le]
    exact le_total _ _
  le_antisymm a b := by
    simp only [le_iff_toList_le, ← toList_inj]
    apply le_antisymm
  lt_iff_le_not_le a b := by
    simp only [le_iff_toList_le, lt_iff_toList_lt, lt_iff_le_not_le]

end String

open String

theorem List.to_list_inv_asString (l : List Char) : l.asString.toList = l := by
  cases hl : l.asString
  symm
  injection hl
#align list.to_list_inv_as_string List.to_list_inv_asString

@[simp]
theorem List.length_as_string (l : List Char) : l.asString.length = l.length :=
  rfl
#align list.length_as_string List.length_as_string

@[simp]
theorem List.asString_inj {l l' : List Char} : l.asString = l'.asString ↔ l = l' :=
  ⟨fun h => by rw [← List.to_list_inv_asString l, ← List.to_list_inv_asString l', toList_inj, h],
    fun h => h ▸ rfl⟩
#align list.as_string_inj List.asString_inj

@[simp]
theorem String.length_toList (s : String) : s.toList.length = s.length := by
  rw [← String.asString_inv_toList s, List.to_list_inv_asString, List.length_as_string]
#align string.length_to_list String.length_toList

theorem List.asString_eq {l : List Char} {s : String} : l.asString = s ↔ l = s.toList := by
  rw [← asString_inv_toList s, List.asString_inj, asString_inv_toList s]
#align list.as_string_eq List.asString_eq
