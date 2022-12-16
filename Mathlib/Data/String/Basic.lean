/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.List.Lex
import Mathlib.Data.Char
import Std.Tactic.RCases

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

-- TODO This proof probably has to be completely redone
@[simp]
theorem lt_iff_toList_lt : ∀ {s₁ s₂ : String}, s₁ < s₂ ↔ s₁.toList < s₂.toList := by
  rintro ⟨s₁⟩ ⟨s₂⟩
  induction s₁ generalizing s₂ <;> simp only [lt']
  case nil =>
    unfold ltb
    simp
    cases s₂
    case nil => simp
    case cons hd tl =>
      simp [LT.lt, toList, List.Lex.nil, mkIterator]
      sorry
  case cons hd tl ih =>
    simp [toList]
    unfold ltb
    split_ifs <;> simp <;> sorry

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
    rfl

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
