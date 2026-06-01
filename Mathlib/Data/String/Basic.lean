/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Batteries.Data.String.Lemmas
public import Mathlib.Data.List.Lex
public import Mathlib.Data.Char
public import Mathlib.Algebra.Order.Group.Nat
import all Init.Data.String.Iterator  -- for unfolding `Iterator.curr`
import all Init.Data.Ord.String  -- for unfolding `String.compare`

/-!
# Strings

Supplementary theorems about the `String` type.
-/

@[expose] public section

namespace String

/-- `<` on string iterators. This coincides with `<` on strings as lists. -/
def ltb (s₁ s₂ : Legacy.Iterator) : Bool :=
  if s₂.hasNext then
    if s₁.hasNext then
      if s₁.curr = s₂.curr then
        ltb s₁.next s₂.next
      else s₁.curr < s₂.curr
    else true
  else false

@[no_expose] def ltb.inductionOn.{u} {motive : Legacy.Iterator → Legacy.Iterator → Sort u}
    (it₁ it₂ : Legacy.Iterator)
    (ind : ∀ s₁ s₂ i₁ i₂, Legacy.Iterator.hasNext ⟨s₂, i₂⟩ → Legacy.Iterator.hasNext ⟨s₁, i₁⟩ →
      i₁.get s₁ = i₂.get s₂ →
        motive (Legacy.Iterator.next ⟨s₁, i₁⟩) (Legacy.Iterator.next ⟨s₂, i₂⟩) →
          motive ⟨s₁, i₁⟩ ⟨s₂, i₂⟩)
    (eq : ∀ s₁ s₂ i₁ i₂, Legacy.Iterator.hasNext ⟨s₂, i₂⟩ → Legacy.Iterator.hasNext ⟨s₁, i₁⟩ →
      ¬ i₁.get s₁ = i₂.get s₂ → motive ⟨s₁, i₁⟩ ⟨s₂, i₂⟩)
    (base₁ : ∀ s₁ s₂ i₁ i₂, Legacy.Iterator.hasNext ⟨s₂, i₂⟩ → ¬ Legacy.Iterator.hasNext ⟨s₁, i₁⟩ →
      motive ⟨s₁, i₁⟩ ⟨s₂, i₂⟩)
    (base₂ : ∀ s₁ s₂ i₁ i₂, ¬ Legacy.Iterator.hasNext ⟨s₂, i₂⟩ → motive ⟨s₁, i₁⟩ ⟨s₂, i₂⟩) :
    motive it₁ it₂ :=
  if h₂ : it₂.hasNext then
    if h₁ : it₁.hasNext then
      if heq : it₁.curr = it₂.curr then
        ind it₁.s it₂.s it₁.i it₂.i h₂ h₁ heq (inductionOn it₁.next it₂.next ind eq base₁ base₂)
      else eq it₁.s it₂.s it₁.i it₂.i h₂ h₁ heq
    else base₁ it₁.s it₂.s it₁.i it₂.i h₂ h₁
  else base₂ it₁.s it₂.s it₁.i it₂.i h₂

theorem ltb_cons_addChar' (c : Char) (s₁ s₂ : Legacy.Iterator) :
    ltb ⟨ofList (c :: s₁.s.toList), s₁.i + c⟩ ⟨ofList (c :: s₂.s.toList), s₂.i + c⟩ =
      ltb s₁ s₂ := by
  fun_induction ltb s₁ s₂ with
  | case1 s₁ s₂ h₁ h₂ h ih =>
    rw [ltb, Legacy.Iterator.hasNext_cons_addChar, Legacy.Iterator.hasNext_cons_addChar,
      if_pos (by simpa using h₁), if_pos (by simpa using h₂), if_pos, ← ih]
    · simp only [Legacy.Iterator.next, Pos.Raw.next, get_cons_addChar, ofList_toList]
      congr 2 <;> apply Pos.Raw.add_char_right_comm
    · simpa only [Legacy.Iterator.curr, get_cons_addChar, ofList_toList] using h
  | case2 s₁ s₂ h₁ h₂ h =>
    rw [ltb, Legacy.Iterator.hasNext_cons_addChar, Legacy.Iterator.hasNext_cons_addChar,
      if_pos (by simpa using h₁), if_pos (by simpa using h₂), if_neg]
    · simp only [Legacy.Iterator.curr, get_cons_addChar, ofList_toList, decide_eq_decide]
    · simpa only [Legacy.Iterator.curr, get_cons_addChar, ofList_toList] using h
  | case3 s₁ s₂ h₁ h₂ =>
    rw [ltb, Legacy.Iterator.hasNext_cons_addChar, Legacy.Iterator.hasNext_cons_addChar,
      if_pos (by simpa using h₁), if_neg (by simpa using h₂)]
  | case4 s₁ s₂ h₁ =>
    rw [ltb, Legacy.Iterator.hasNext_cons_addChar, if_neg (by simpa using h₁)]

theorem ltb_cons_addChar (c : Char) (cs₁ cs₂ : List Char) (i₁ i₂ : Pos.Raw) :
    ltb ⟨ofList (c :: cs₁), i₁ + c⟩ ⟨ofList (c :: cs₂), i₂ + c⟩ =
      ltb ⟨ofList cs₁, i₁⟩ ⟨ofList cs₂, i₂⟩ := by
  rw [eq_comm, ← ltb_cons_addChar' c]
  simp

@[deprecated "Use the new String API" (since := "2026-04-01")]
theorem toList_nonempty :
    ∀ {s : String}, s ≠ "" → s.toList = String.Legacy.front s :: (String.Legacy.drop s 1).toList
  | s, h => by
    obtain ⟨l, rfl⟩ := s.exists_eq_ofList
    match l with
    | [] => simp at h
    | c::cs => simp [Legacy.front, Pos.Raw.get, Pos.Raw.utf8GetAux]

@[simp]
theorem head_empty : "".toList.head! = default :=
  rfl

theorem lt_iff_toList_lt {s₁ s₂ : String} : s₁ < s₂ ↔ s₁.toList < s₂.toList :=
  Iff.rfl

protected theorem le_iff_not_lt {s₁ s₂ : String} : s₁ ≤ s₂ ↔ ¬ s₂ < s₁ :=
  Iff.rfl

theorem le_iff_toList_le {s₁ s₂ : String} : s₁ ≤ s₂ ↔ s₁.toList ≤ s₂.toList := by
  rw [String.le_iff_not_lt, lt_iff_toList_lt, not_lt]

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
  toDecidableLE := inferInstance
  toDecidableEq := inferInstance
  toDecidableLT := String.decidableLT
  compare_eq_compareOfLessAndEq a b := by simp [Ord.compare, String.compare]

theorem ofList_eq {l : List Char} {s : String} : ofList l = s ↔ l = s.toList := by
  simp [← toList_inj]

end String
