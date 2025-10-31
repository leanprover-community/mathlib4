/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Batteries.Data.String.Lemmas
import Mathlib.Data.List.Lex
import Mathlib.Data.Char
import Mathlib.Algebra.Order.Group.Nat

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

/-- This overrides an instance in core Lean. -/
instance LT' : LT String :=
  ⟨fun s₁ s₂ ↦ ltb s₁.iter s₂.iter⟩

/-- This instance has a prime to avoid the name of the corresponding instance in core Lean. -/
instance decidableLT' : DecidableLT String := by
  simp only [DecidableLT, LT']
  infer_instance -- short-circuit type class inference

/-- Induction on `String.ltb`. -/
def ltb.inductionOn.{u} {motive : Iterator → Iterator → Sort u} (it₁ it₂ : Iterator)
    (ind : ∀ s₁ s₂ i₁ i₂, Iterator.hasNext ⟨s₂, i₂⟩ → Iterator.hasNext ⟨s₁, i₁⟩ →
      i₁.get s₁ = i₂.get s₂ → motive (Iterator.next ⟨s₁, i₁⟩) (Iterator.next ⟨s₂, i₂⟩) →
      motive ⟨s₁, i₁⟩ ⟨s₂, i₂⟩)
    (eq : ∀ s₁ s₂ i₁ i₂, Iterator.hasNext ⟨s₂, i₂⟩ → Iterator.hasNext ⟨s₁, i₁⟩ →
      ¬ i₁.get s₁ = i₂.get s₂ → motive ⟨s₁, i₁⟩ ⟨s₂, i₂⟩)
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

theorem ltb_cons_addChar' (c : Char) (s₁ s₂ : Iterator) :
    ltb ⟨mk (c :: s₁.s.data), s₁.i + c⟩ ⟨mk (c :: s₂.s.data), s₂.i + c⟩ = ltb s₁ s₂ := by
  fun_induction ltb s₁ s₂ with
  | case1 s₁ s₂ h₁ h₂ h ih =>
    rw [ltb, Iterator.hasNext_cons_addChar, Iterator.hasNext_cons_addChar,
      if_pos (by simpa using h₁), if_pos (by simpa using h₂), if_pos, ← ih]
    · simp [Iterator.next, String.Pos.Raw.next, get_cons_addChar]
      congr 2 <;> apply Pos.Raw.add_char_right_comm
    · simpa [Iterator.curr, get_cons_addChar] using h
  | case2 s₁ s₂ h₁ h₂ h =>
    rw [ltb, Iterator.hasNext_cons_addChar, Iterator.hasNext_cons_addChar,
      if_pos (by simpa using h₁), if_pos (by simpa using h₂), if_neg]
    · simp [Iterator.curr, get_cons_addChar]
    · simpa [Iterator.curr, get_cons_addChar] using h
  | case3 s₁ s₂ h₁ h₂ =>
    rw [ltb, Iterator.hasNext_cons_addChar, Iterator.hasNext_cons_addChar,
      if_pos (by simpa using h₁), if_neg (by simpa using h₂)]
  | case4 s₁ s₂ h₁ =>
    rw [ltb, Iterator.hasNext_cons_addChar, if_neg (by simpa using h₁)]

theorem ltb_cons_addChar (c : Char) (cs₁ cs₂ : List Char) (i₁ i₂ : Pos.Raw) :
    ltb ⟨mk (c :: cs₁), i₁ + c⟩ ⟨mk (c :: cs₂), i₂ + c⟩ = ltb ⟨mk cs₁, i₁⟩ ⟨mk cs₂, i₂⟩ := by
  rw [eq_comm, ← ltb_cons_addChar' c]
  simp

@[simp]
theorem lt_iff_toList_lt : ∀ {s₁ s₂ : String}, s₁ < s₂ ↔ s₁.toList < s₂.toList
  | s₁, s₂ => show ltb ⟨s₁, 0⟩ ⟨s₂, 0⟩ ↔ s₁.data < s₂.data by
    obtain ⟨s₁, rfl⟩ := s₁.exists_eq_asString
    obtain ⟨s₂, rfl⟩ := s₂.exists_eq_asString
    simp only [List.data_asString]
    induction s₁ generalizing s₂ <;> cases s₂
    · unfold ltb; decide
    · rename_i c₂ cs₂; apply iff_of_true
      · unfold ltb
        simp [Iterator.hasNext, Char.utf8Size_pos]
      · apply List.nil_lt_cons
    · rename_i c₁ cs₁ ih; apply iff_of_false
      · unfold ltb
        simp [Iterator.hasNext]
      · apply not_lt_of_gt; apply List.nil_lt_cons
    · rename_i c₁ cs₁ ih c₂ cs₂; unfold ltb
      simp only [Iterator.hasNext, Pos.Raw.byteIdx_zero, rawEndPos_asString, utf8Len_cons,
        add_pos_iff, Char.utf8Size_pos, or_true, decide_true, ↓reduceIte, Iterator.curr,
        Pos.Raw.get, List.data_asString, Pos.Raw.utf8GetAux, Iterator.next, Pos.Raw.next,
        Bool.ite_eq_true_distrib, decide_eq_true_eq]
      simp only [← String.mk_eq_asString]
      split_ifs with h
      · subst c₂
        suffices ltb ⟨mk (c₁ :: cs₁), (0 : Pos.Raw) + c₁⟩ ⟨mk (c₁ :: cs₂), (0 : Pos.Raw) + c₁⟩ =
          ltb ⟨mk cs₁, 0⟩ ⟨mk cs₂, 0⟩ by rw [this]; exact (ih cs₂).trans List.lex_cons_iff.symm
        apply ltb_cons_addChar
      · refine ⟨List.Lex.rel, fun e ↦ ?_⟩
        cases e <;> rename_i h'
        · assumption
        · contradiction

instance LE : LE String :=
  ⟨fun s₁ s₂ ↦ ¬s₂ < s₁⟩

instance decidableLE : DecidableLE String := by
  simp only [DecidableLE, LE]
  infer_instance -- short-circuit type class inference

@[simp]
theorem le_iff_toList_le {s₁ s₂ : String} : s₁ ≤ s₂ ↔ s₁.toList ≤ s₂.toList :=
  (not_congr lt_iff_toList_lt).trans not_lt

@[simp]
theorem toList_eq_data {s : String} : s.toList = s.data := rfl

#adaptation_note /-- 2025-10-31
  Will be cleaned up in https://github.com/leanprover/lean4/pull/11017 -/
attribute [-simp] toList

theorem toList_inj {s₁ s₂ : String} : s₁.toList = s₂.toList ↔ s₁ = s₂ := by
  simp [data_inj]

theorem asString_nil : [].asString = "" :=
  rfl

theorem toList_empty : "".toList = [] :=
  rfl

theorem asString_toList (s : String) : s.toList.asString = s := by
  simp

theorem toList_nonempty : ∀ {s : String}, s ≠ "" → s.toList = s.head :: (s.drop 1).toList
  | s, h => by
    obtain ⟨l, rfl⟩ := s.exists_eq_asString
    match l with
    | [] => simp at h
    | c::cs => simp [head, mkIterator, Iterator.curr, Pos.Raw.get, Pos.Raw.utf8GetAux]

@[simp]
theorem head_empty : "".data.head! = default :=
  rfl

instance : LinearOrder String where
  le_refl _ := le_iff_toList_le.mpr le_rfl
  le_trans a b c := by
    simp only [le_iff_toList_le]
    apply le_trans
  lt_iff_le_not_ge a b := by
    simp only [lt_iff_toList_lt, le_iff_toList_le, lt_iff_le_not_ge]
  le_antisymm a b := by
    simp only [le_iff_toList_le, ← toList_inj]
    apply le_antisymm
  le_total a b := by
    simp only [le_iff_toList_le]
    apply le_total
  toDecidableLE := String.decidableLE
  toDecidableEq := inferInstance
  toDecidableLT := String.decidableLT'
  compare_eq_compareOfLessAndEq a b := by
    simp only [compare, compareOfLessAndEq, instLT, List.instLT, lt_iff_toList_lt, toList_eq_data]
    split_ifs <;>
    simp only [List.lt_iff_lex_lt] at *

end String

open String

namespace List

theorem toList_asString (l : List Char) : l.asString.toList = l := by
  simp [-toList]

theorem asString_eq {l : List Char} {s : String} : l.asString = s ↔ l = s.toList := by
  rw [← asString_toList s, asString_inj, asString_toList s]

end List
