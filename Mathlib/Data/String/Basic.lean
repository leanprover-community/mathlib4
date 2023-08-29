/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.List.Lex
import Mathlib.Data.Char

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
  -- ⊢ DecidableRel fun s₁ s₂ => ltb (iter s₁) (iter s₂) = true
  infer_instance -- short-circuit type class inference
  -- 🎉 no goals
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
    ltb ⟨⟨cs₁⟩, i₁⟩ ⟨⟨cs₂⟩, i₂⟩) <;> simp <;>
                                     -- ⊢ ∀ (s₁ s₂ : String) (i₁ i₂ : Pos), Iterator.hasNext { s := s₂, i := i₂ } = tr …
                                     -- ⊢ ∀ (s₁ s₂ : String) (i₁ i₂ : Pos), Iterator.hasNext { s := s₂, i := i₂ } = tr …
                                     -- ⊢ ∀ (s₁ s₂ : String) (i₁ i₂ : Pos), Iterator.hasNext { s := s₂, i := i₂ } = tr …
                                     -- ⊢ ∀ (s₁ s₂ : String) (i₁ i₂ : Pos), Iterator.hasNext { s := s₂, i := i₂ } = fa …
  intro ⟨cs₁⟩ ⟨cs₂⟩ i₁ i₂ <;>
  -- ⊢ Iterator.hasNext { s := { data := cs₂ }, i := i₂ } = true → Iterator.hasNext …
  -- ⊢ Iterator.hasNext { s := { data := cs₂ }, i := i₂ } = true → Iterator.hasNext …
  -- ⊢ Iterator.hasNext { s := { data := cs₂ }, i := i₂ } = true → Iterator.hasNext …
  -- ⊢ Iterator.hasNext { s := { data := cs₂ }, i := i₂ } = false → ltb { s := { da …
  intros <;>
  -- ⊢ ltb { s := { data := c :: { data := cs₁ }.data }, i := i₁ + c } { s := { dat …
  -- ⊢ ltb { s := { data := c :: { data := cs₁ }.data }, i := i₁ + c } { s := { dat …
  -- ⊢ ltb { s := { data := c :: { data := cs₁ }.data }, i := i₁ + c } { s := { dat …
  -- ⊢ ltb { s := { data := c :: { data := cs₁ }.data }, i := i₁ + c } { s := { dat …
  (conv => lhs; rw [ltb]) <;> (conv => rhs; rw [ltb]) <;>
   -- ⊢ (if Iterator.hasNext { s := { data := c :: { data := cs₂ }.data }, i := i₂ + …
   -- ⊢ (if Iterator.hasNext { s := { data := c :: { data := cs₂ }.data }, i := i₂ + …
   -- ⊢ (if Iterator.hasNext { s := { data := c :: { data := cs₂ }.data }, i := i₂ + …
   -- ⊢ (if Iterator.hasNext { s := { data := c :: { data := cs₂ }.data }, i := i₂ + …
                               -- ⊢ (if Iterator.hasNext { s := { data := c :: { data := cs₂ }.data }, i := i₂ + …
                               -- ⊢ (if Iterator.hasNext { s := { data := c :: { data := cs₂ }.data }, i := i₂ + …
                               -- ⊢ (if Iterator.hasNext { s := { data := c :: { data := cs₂ }.data }, i := i₂ + …
                               -- ⊢ (if Iterator.hasNext { s := { data := c :: { data := cs₂ }.data }, i := i₂ + …
  simp [Iterator.hasNext_cons_addChar, *]
  -- ⊢ (if Iterator.curr { s := { data := c :: cs₁ }, i := i₁ + c } = Iterator.curr …
  -- ⊢ (if Iterator.curr { s := { data := c :: cs₁ }, i := i₁ + c } = Iterator.curr …
  -- 🎉 no goals
  -- 🎉 no goals
  · rename_i h₂ h₁ heq ih
    -- ⊢ (if Iterator.curr { s := { data := c :: cs₁ }, i := i₁ + c } = Iterator.curr …
    simp [Iterator.curr, get_cons_addChar, Iterator.next, next, *] at *
    -- ⊢ ltb { s := { data := c :: cs₁ }, i := i₁ + c + get { data := cs₂ } i₂ } { s  …
    repeat rw [Pos.addChar_right_comm _ c]
    -- ⊢ ltb { s := { data := c :: cs₁ }, i := i₁ + get { data := cs₂ } i₂ + c } { s  …
    exact ih
    -- 🎉 no goals
  · rename_i h₂ h₁ hne
    -- ⊢ (if Iterator.curr { s := { data := c :: cs₁ }, i := i₁ + c } = Iterator.curr …
    simp [Iterator.curr, get_cons_addChar, *]
    -- 🎉 no goals

@[simp]
theorem lt_iff_toList_lt : ∀ {s₁ s₂ : String}, s₁ < s₂ ↔ s₁.toList < s₂.toList
| ⟨s₁⟩, ⟨s₂⟩ => show ltb ⟨⟨s₁⟩, 0⟩ ⟨⟨s₂⟩, 0⟩ ↔ s₁ < s₂ by
  induction s₁ generalizing s₂ <;> cases s₂
  -- ⊢ ltb { s := { data := [] }, i := 0 } { s := { data := s₂ }, i := 0 } = true ↔ …
                                   -- ⊢ ltb { s := { data := [] }, i := 0 } { s := { data := [] }, i := 0 } = true ↔ …
                                   -- ⊢ ltb { s := { data := head✝ :: tail✝ }, i := 0 } { s := { data := [] }, i :=  …
  · simp
    -- 🎉 no goals
  · rename_i c₂ cs₂; apply iff_of_true
    -- ⊢ ltb { s := { data := [] }, i := 0 } { s := { data := c₂ :: cs₂ }, i := 0 } = …
                     -- ⊢ ltb { s := { data := [] }, i := 0 } { s := { data := c₂ :: cs₂ }, i := 0 } = …
    · rw [ltb]; simp; apply ne_false_of_eq_true; apply decide_eq_true
      -- ⊢ (if Iterator.hasNext { s := { data := c₂ :: cs₂ }, i := 0 } = true then if I …
                -- ⊢ Iterator.hasNext { s := { data := c₂ :: cs₂ }, i := 0 } = false → False
                      -- ⊢ Iterator.hasNext { s := { data := c₂ :: cs₂ }, i := 0 } = true
                                                 -- ⊢ 0.byteIdx < (endPos { data := c₂ :: cs₂ }).byteIdx
      simp [endPos, utf8ByteSize, utf8ByteSize.go, csize_pos]
      -- 🎉 no goals
    · apply List.nil_lt_cons
      -- 🎉 no goals
  · rename_i c₁ cs₁ ih; apply iff_of_false
    -- ⊢ ltb { s := { data := c₁ :: cs₁ }, i := 0 } { s := { data := [] }, i := 0 } = …
                        -- ⊢ ¬ltb { s := { data := c₁ :: cs₁ }, i := 0 } { s := { data := [] }, i := 0 }  …
    · rw [ltb]; simp
      -- ⊢ ¬(if Iterator.hasNext { s := { data := [] }, i := 0 } = true then if Iterato …
                -- 🎉 no goals
    · apply not_lt_of_lt; apply List.nil_lt_cons
      -- ⊢ [] < c₁ :: cs₁
                          -- 🎉 no goals
  · rename_i c₁ cs₁ ih c₂ cs₂; rw [ltb]
    -- ⊢ ltb { s := { data := c₁ :: cs₁ }, i := 0 } { s := { data := c₂ :: cs₂ }, i : …
                               -- ⊢ (if Iterator.hasNext { s := { data := c₂ :: cs₂ }, i := 0 } = true then if I …
    simp [Iterator.hasNext, endPos, utf8ByteSize, utf8ByteSize.go, csize_pos, Iterator.curr, get,
          utf8GetAux, Iterator.next, next]
    split_ifs with h
    -- ⊢ ltb { s := { data := c₁ :: cs₁ }, i := 0 + c₁ } { s := { data := c₂ :: cs₂ } …
    · subst c₂
      -- ⊢ ltb { s := { data := c₁ :: cs₁ }, i := 0 + c₁ } { s := { data := c₁ :: cs₂ } …
      suffices ltb ⟨⟨c₁ :: cs₁⟩, ⟨csize c₁⟩⟩ ⟨⟨c₁ :: cs₂⟩, ⟨csize c₁⟩⟩ = ltb ⟨⟨cs₁⟩, 0⟩ ⟨⟨cs₂⟩, 0⟩
        by rw [Pos.zero_addChar_eq, this]; exact (ih cs₂).trans List.Lex.cons_iff.symm
      rw [← Pos.zero_addChar_eq]
      -- ⊢ ltb { s := { data := c₁ :: cs₁ }, i := 0 + c₁ } { s := { data := c₁ :: cs₂ } …
      apply ltb_cons_addChar
      -- 🎉 no goals
    · refine ⟨List.Lex.rel, fun e ↦ ?_⟩
      -- ⊢ c₁ < c₂
      cases e <;> rename_i h'
      -- ⊢ c₁ < c₁
                  -- ⊢ c₁ < c₁
                  -- ⊢ c₁ < c₂
      · contradiction
        -- 🎉 no goals
      · assumption
        -- 🎉 no goals
#align string.lt_iff_to_list_lt String.lt_iff_toList_lt

instance LE : LE String :=
  ⟨fun s₁ s₂ ↦ ¬s₂ < s₁⟩
#align string.has_le String.LE

instance decidableLE : @DecidableRel String (· ≤ ·) := by
  simp only [LE]
  -- ⊢ DecidableRel fun s₁ s₂ => ¬s₂ < s₁
  infer_instance -- short-circuit type class inference
  -- 🎉 no goals
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

#align string.to_list_singleton String.data_singleton

theorem toList_nonempty : ∀ {s : String}, s ≠ "" → s.toList = s.head :: (s.drop 1).toList
| ⟨s⟩, h => by
  cases s
  -- ⊢ toList { data := [] } = head { data := [] } :: toList (drop { data := [] } 1)
  · simp only at h
    -- 🎉 no goals
  · rename_i c cs
    -- ⊢ toList { data := c :: cs } = head { data := c :: cs } :: toList (drop { data …
    simp only [toList, List.cons.injEq]
    -- ⊢ c = head { data := c :: cs } ∧ cs = (drop { data := c :: cs } 1).data
    constructor <;> [rfl; simp [drop_eq]]
    -- 🎉 no goals
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
    -- ⊢ toList a ≤ toList b → toList b ≤ toList c → toList a ≤ toList c
    apply le_trans
    -- 🎉 no goals
  lt_iff_le_not_le a b := by
    simp only [lt_iff_toList_lt, le_iff_toList_le, lt_iff_le_not_le]
    -- 🎉 no goals
  le_antisymm a b := by
    simp only [le_iff_toList_le, ← toList_inj]
    -- ⊢ toList a ≤ toList b → toList b ≤ toList a → toList a = toList b
    apply le_antisymm
    -- 🎉 no goals
  le_total a b := by
    simp only [le_iff_toList_le]
    -- ⊢ toList a ≤ toList b ∨ toList b ≤ toList a
    apply le_total
    -- 🎉 no goals
  decidableLE := String.decidableLE
  compare_eq_compareOfLessAndEq a b := by
    simp [compare, compareOfLessAndEq, toList, instLTString, List.instLTList, List.LT']
    -- ⊢ (if List.lt a.data b.data then Ordering.lt else if a = b then Ordering.eq el …
    split_ifs <;>
    simp [List.lt_iff_lex_lt] at * <;>
    -- 🎉 no goals
    -- ⊢ False
    -- ⊢ False
    -- ⊢ False
    -- 🎉 no goals
    -- ⊢ False
    -- 🎉 no goals
    contradiction
    -- 🎉 no goals
    -- 🎉 no goals
    -- 🎉 no goals
    -- 🎉 no goals

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
              -- 🎉 no goals
   fun h ↦ h ▸ rfl⟩
#align list.as_string_inj List.asString_inj

@[simp]
theorem String.length_data (s : String) : s.data.length = s.length :=
  rfl
#align string.length_to_list String.length_data

theorem List.asString_eq {l : List Char} {s : String} : l.asString = s ↔ l = s.toList := by
  rw [← asString_inv_toList s, asString_inj, asString_inv_toList s]
  -- 🎉 no goals
#align list.as_string_eq List.asString_eq
