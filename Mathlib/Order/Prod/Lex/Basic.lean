/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Minchao Wu
-/
module

public import Mathlib.Data.Prod.Basic
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.Lattice
public import Mathlib.Order.Lex
public import Mathlib.Tactic.Tauto

/-!
# Lexicographic order

This file defines the lexicographic relation for pairs of orders, partial orders and linear orders.

## Main declarations

* `Prod.Lex.<pre/partial/linear>Order`: Instances lifting the orders on `α` and `β` to `α ×ₗ β`.

## Notation

* `α ×ₗ β`: `α × β` equipped with the lexicographic order

## See also

Related files are:
* `Data.Finset.CoLex`: Colexicographic order on finite sets.
* `Data.List.Lex`: Lexicographic order on lists.
* `Data.Pi.Lex`: Lexicographic order on `Πₗ i, α i`.
* `Order.PSigma`: Lexicographic order on `Σ' i, α i`.
* `Order.Sigma`: Lexicographic order on `Σ i, α i`.

## TODO

Some lemmas could be automatically generated with `to_dual`.
See [https://github.com/leanprover-community/mathlib4/pull/37939#discussion_r3367855484]
-/

public section

variable {α β : Type*}

open Lex

namespace Prod.Lex

@[inherit_doc] notation:35 α " ×ₗ " β:34 => Lex (α × β)

instance (α β : Type*) [LT α] [LE β] : LE (α ×ₗ β) where
  le x y := Prod.Lex (· < ·) (· ≤ ·) x.ofLex y.ofLex

instance instLT (α β : Type*) [LT α] [LT β] : LT (α ×ₗ β) where
  lt x y := Prod.Lex (· < ·) (· < ·) x.ofLex y.ofLex

theorem toLex_le_toLex [LT α] [LE β] {x y : α × β} :
    toLex x ≤ toLex y ↔ x.1 < y.1 ∨ x.1 = y.1 ∧ x.2 ≤ y.2 :=
  Prod.lex_def

to_dual_for toLex_le_toLex := by rw [eq_comm, toLex_le_toLex]

theorem toLex_lt_toLex [LT α] [LT β] {x y : α × β} :
    toLex x < toLex y ↔ x.1 < y.1 ∨ x.1 = y.1 ∧ x.2 < y.2 :=
  Prod.lex_def

to_dual_for toLex_lt_toLex := by rw [eq_comm, toLex_lt_toLex]

@[to_dual none]
lemma le_iff [LT α] [LE β] {x y : α ×ₗ β} :
    x ≤ y ↔ x.ofLex.1 < y.ofLex.1 ∨ x.ofLex.1 = y.ofLex.1 ∧ x.ofLex.2 ≤ y.ofLex.2 :=
  toLex_le_toLex

@[to_dual none]
lemma lt_iff [LT α] [LT β] {x y : α ×ₗ β} :
    x < y ↔ x.ofLex.1 < y.ofLex.1 ∨ x.ofLex.1 = y.ofLex.1 ∧ x.ofLex.2 < y.ofLex.2 :=
  toLex_lt_toLex

instance [LT α] [LT β] [WellFoundedLT α] [WellFoundedLT β] : WellFoundedLT (α ×ₗ β) :=
  InvImage.wf Lex.ofLex (wellFounded_lt.prod_lex wellFounded_lt)

instance [LT α] [LT β] [WellFoundedLT α] [WellFoundedLT β] : WellFoundedRelation (α ×ₗ β) :=
  WellFoundedLT.toWellFoundedRelation

instance (α β : Type*) [Preorder α] [Preorder β] : Preorder (α ×ₗ β) where
  le_refl := by simp [toLex_le_toLex]
  le_trans _ _ _ := trans_of <| Prod.Lex _ _
  lt_iff_le_not_ge x₁ x₂ := by grind [le_iff, lt_iff, lt_iff_le_not_ge]

/-- See also `monotone_fst_ofLex` for a version stated in terms of `Monotone`. -/
theorem monotone_fst [Preorder α] [LE β] (t c : α ×ₗ β) (h : t ≤ c) :
    (ofLex t).1 ≤ (ofLex c).1 := by
  cases toLex_le_toLex.mp h with
  | inl h' => exact h'.le
  | inr h' => exact h'.1.le

section Preorder

variable [Preorder α] [Preorder β]

theorem monotone_fst_ofLex : Monotone fun x : α ×ₗ β ↦ x.ofLex.1 := monotone_fst

@[to_dual self]
theorem _root_.WCovBy.fst_ofLex {a b : α ×ₗ β} (h : a ⩿ b) : a.ofLex.1 ⩿ b.ofLex.1 :=
  ⟨monotone_fst _ _ h.1, fun c hac hcb ↦
    h.2 (c := toLex (c, a.ofLex.2)) (.left _ _ hac) (.left _ _ hcb)⟩

@[to_dual none]
theorem toLex_covBy_toLex_iff {a₁ a₂ : α} {b₁ b₂ : β} :
    toLex (a₁, b₁) ⋖ toLex (a₂, b₂) ↔ a₁ = a₂ ∧ b₁ ⋖ b₂ ∨ a₁ ⋖ a₂ ∧ IsMax b₁ ∧ IsMin b₂ := by
  simp only [CovBy, toLex_lt_toLex, Lex.forall, Prod.forall, isMax_iff_forall_not_lt,
    isMin_iff_forall_not_lt]
  grind

@[to_dual none]
theorem covBy_iff {a b : α ×ₗ β} :
    a ⋖ b ↔ a.ofLex.1 = b.ofLex.1 ∧ a.ofLex.2 ⋖ b.ofLex.2 ∨
      a.ofLex.1 ⋖ b.ofLex.1 ∧ IsMax a.ofLex.2 ∧ IsMin b.ofLex.2 :=
  toLex_covBy_toLex_iff

end Preorder

section PartialOrderPreorder

variable [PartialOrder α] [Preorder β] {x y : α × β}

/-- Variant of `Prod.Lex.toLex_le_toLex` for partial orders. -/
@[to_dual none]
lemma toLex_le_toLex' : toLex x ≤ toLex y ↔ x.1 ≤ y.1 ∧ (x.1 = y.1 → x.2 ≤ y.2) := by
  simp only [toLex_le_toLex, lt_iff_le_not_ge, le_antisymm_iff]
  tauto

/-- Variant of `Prod.Lex.toLex_lt_toLex` for partial orders. -/
@[to_dual none]
lemma toLex_lt_toLex' : toLex x < toLex y ↔ x.1 ≤ y.1 ∧ (x.1 = y.1 → x.2 < y.2) := by
  rw [toLex_lt_toLex]
  simp only [lt_iff_le_not_ge, le_antisymm_iff]
  tauto

/-- Variant of `Prod.Lex.le_iff` for partial orders. -/
@[to_dual none]
lemma le_iff' {x y : α ×ₗ β} :
    x ≤ y ↔ x.ofLex.1 ≤ y.ofLex.1 ∧ (x.ofLex.1 = y.ofLex.1 → x.ofLex.2 ≤ y.ofLex.2) :=
  toLex_le_toLex'

/-- Variant of `Prod.Lex.lt_iff` for partial orders. -/
@[to_dual none]
lemma lt_iff' {x y : α ×ₗ β} :
    x < y ↔ x.ofLex.1 ≤ y.ofLex.1 ∧ (x.ofLex.1 = y.ofLex.1 → x.ofLex.2 < y.ofLex.2) :=
  toLex_lt_toLex'

theorem toLex_mono : Monotone (toLex : α × β → α ×ₗ β) :=
  fun _x _y hxy ↦ toLex_le_toLex'.2 ⟨hxy.1, fun _ ↦ hxy.2⟩

theorem toLex_strictMono : StrictMono (toLex : α × β → α ×ₗ β) := by
  rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h
  obtain rfl | ha : a₁ = a₂ ∨ _ := h.le.1.eq_or_lt
  · exact right _ (Prod.mk_lt_mk_iff_right.1 h)
  · exact left _ _ ha

end PartialOrderPreorder

instance (α β : Type*) [PartialOrder α] [PartialOrder β] : PartialOrder (α ×ₗ β) where
  le_antisymm _ _ h₁ h₂ := Lex.ext (antisymm_of (Prod.Lex _ _) h₁ h₂)

instance [Ord α] [Ord β] : Ord (α ×ₗ β) where
  compare := compareLex (compareOn (·.ofLex.1)) (compareOn (·.ofLex.2))

theorem compare_def [Ord α] [Ord β] : @compare (α ×ₗ β) _ =
    compareLex (compareOn (·.ofLex.1)) (compareOn (·.ofLex.2)) := rfl

@[deprecated "type changed" (since := "2026-11-09")] alias _root_.lexOrd_eq := compare_def
@[deprecated "type changed" (since := "2026-11-09")] alias _root_.Ord.lex_eq := compare_def

instance [Ord α] [Ord β] [Std.OrientedOrd α] [Std.OrientedOrd β] : Std.OrientedOrd (α ×ₗ β) :=
  inferInstanceAs (Std.OrientedCmp (compareLex _ _))

instance [Ord α] [Ord β] [Std.TransOrd α] [Std.TransOrd β] : Std.TransOrd (α ×ₗ β) :=
  inferInstanceAs (Std.TransCmp (compareLex _ _))

instance (α β : Type*) [LinearOrder α] [LinearOrder β] : LinearOrder (α ×ₗ β) where
  le_total x y := total_of (Prod.Lex _ _) x.ofLex y.ofLex
  toDecidableLE x y := Prod.Lex.decidable _ _ x.ofLex y.ofLex
  toDecidableLT x y := Prod.Lex.decidable _ _ x.ofLex y.ofLex
  toDecidableEq := inferInstance
  compare_eq_compareOfLessAndEq a b := by
    have : DecidableLT (α ×ₗ β) := fun x y ↦ Prod.Lex.decidable _ _ x.ofLex y.ofLex
    have : Std.LawfulBEqOrd (α ×ₗ β) := ⟨by
      simp [compare_def, compareLex, compareOn, Ordering.then_eq_eq]⟩
    have : Std.LawfulLTOrd (α ×ₗ β) := ⟨by
      simp [compare_def, compareLex, compareOn, Ordering.then_eq_lt, lt_iff,
        compare_lt_iff_lt]⟩
    convert Std.LawfulLTCmp.eq_compareOfLessAndEq (cmp := compare) a b

@[to_dual]
instance orderBot [PartialOrder α] [Preorder β] [OrderBot α] [OrderBot β] : OrderBot (α ×ₗ β) where
  bot := toLex ⊥
  bot_le _ := toLex_mono bot_le

instance boundedOrder [PartialOrder α] [Preorder β] [BoundedOrder α] [BoundedOrder β] :
    BoundedOrder (α ×ₗ β) where

instance [Preorder α] [Preorder β] [DenselyOrdered α] [DenselyOrdered β] :
    DenselyOrdered (α ×ₗ β) where
  dense := by
    rintro ⟨_⟩ ⟨_⟩ (@⟨a₁, b₁, a₂, b₂, h⟩ | @⟨a, b₁, b₂, h⟩)
    · obtain ⟨c, h₁, h₂⟩ := exists_between h
      exact ⟨⟨c, b₁⟩, left _ _ h₁, left _ _ h₂⟩
    · obtain ⟨c, h₁, h₂⟩ := exists_between h
      exact ⟨⟨a, c⟩, right _ h₁, right _ h₂⟩

instance [Preorder α] [Preorder β] [NoMinOrder β] [DenselyOrdered β] :
    DenselyOrdered (α ×ₗ β) where
  dense := by
    rintro ⟨x⟩ ⟨y⟩ h
    simp only [Prod.Lex.toLex_lt_toLex] at h
    rcases h with (h | h)
    · obtain ⟨v, hv⟩ := exists_lt y.2
      use toLex (y.1, v)
      simp [Prod.Lex.toLex_lt_toLex, h, hv]
    · obtain ⟨v, htv, hvu⟩ := DenselyOrdered.dense x.2 y.2 h.2
      use toLex (x.1, v)
      simp [Prod.Lex.toLex_lt_toLex, h.1, htv, hvu]

@[to_dual existing]
instance [Preorder α] [Preorder β] [NoMaxOrder β] [DenselyOrdered β] :
    DenselyOrdered (α ×ₗ β) where
  dense := by
    rintro ⟨x⟩ ⟨y⟩ h
    simp only [Prod.Lex.toLex_lt_toLex] at h
    rcases h with (h | h)
    · obtain ⟨v, hv⟩ := exists_gt x.2
      use toLex (x.1, v)
      simp [Prod.Lex.toLex_lt_toLex, h, hv]
    · obtain ⟨v, htv, hvu⟩ := DenselyOrdered.dense x.2 y.2 h.2
      use toLex (x.1, v)
      simp [Prod.Lex.toLex_lt_toLex, h.1, htv, hvu]

@[to_dual]
instance noMaxOrder_of_left [Preorder α] [Preorder β] [NoMaxOrder α] : NoMaxOrder (α ×ₗ β) where
  exists_gt := by
    rw [Lex.forall, Prod.forall]
    intro a b
    obtain ⟨c, h⟩ := exists_gt a
    use toLex (c, b)
    simpa [lt_iff]

@[to_dual]
instance noMaxOrder_of_right [Preorder α] [Preorder β] [NoMaxOrder β] : NoMaxOrder (α ×ₗ β) where
  exists_gt := by
    rw [Lex.forall, Prod.forall]
    intro a b
    obtain ⟨c, h⟩ := exists_gt b
    use toLex (a, c)
    simpa [lt_iff]

end Prod.Lex
