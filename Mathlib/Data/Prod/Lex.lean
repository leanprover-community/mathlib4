/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Minchao Wu
-/
import Mathlib.Order.BoundedOrder

#align_import data.prod.lex from "leanprover-community/mathlib"@"70d50ecfd4900dd6d328da39ab7ebd516abe4025"

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
* `Data.PSigma.Order`: Lexicographic order on `Σ' i, α i`.
* `Data.Sigma.Order`: Lexicographic order on `Σ i, α i`.
-/


variable {α β γ : Type*}

namespace Prod.Lex

@[inherit_doc] notation:35 α " ×ₗ " β:34 => Lex (Prod α β)

instance decidableEq (α β : Type*) [DecidableEq α] [DecidableEq β] : DecidableEq (α ×ₗ β) :=
  instDecidableEqProd
#align prod.lex.decidable_eq Prod.Lex.decidableEq

instance inhabited (α β : Type*) [Inhabited α] [Inhabited β] : Inhabited (α ×ₗ β) :=
  instInhabitedProd
#align prod.lex.inhabited Prod.Lex.inhabited

/-- Dictionary / lexicographic ordering on pairs.  -/
instance instLE (α β : Type*) [LT α] [LE β] : LE (α ×ₗ β) where le := Prod.Lex (· < ·) (· ≤ ·)
#align prod.lex.has_le Prod.Lex.instLE

instance instLT (α β : Type*) [LT α] [LT β] : LT (α ×ₗ β) where lt := Prod.Lex (· < ·) (· < ·)
#align prod.lex.has_lt Prod.Lex.instLT

theorem le_iff [LT α] [LE β] (a b : α × β) :
    toLex a ≤ toLex b ↔ a.1 < b.1 ∨ a.1 = b.1 ∧ a.2 ≤ b.2 :=
  Prod.lex_def (· < ·) (· ≤ ·)
#align prod.lex.le_iff Prod.Lex.le_iff

theorem lt_iff [LT α] [LT β] (a b : α × β) :
    toLex a < toLex b ↔ a.1 < b.1 ∨ a.1 = b.1 ∧ a.2 < b.2 :=
  Prod.lex_def (· < ·) (· < ·)
#align prod.lex.lt_iff Prod.Lex.lt_iff

example (x : α) (y : β) : toLex (x, y) = toLex (x, y) := rfl

/-- Dictionary / lexicographic preorder for pairs. -/
instance preorder (α β : Type*) [Preorder α] [Preorder β] : Preorder (α ×ₗ β) :=
  { Prod.Lex.instLE α β, Prod.Lex.instLT α β with
    le_refl := refl_of <| Prod.Lex _ _,
    le_trans := fun _ _ _ => trans_of <| Prod.Lex _ _,
    lt_iff_le_not_le := fun x₁ x₂ =>
      match x₁, x₂ with
      | (a₁, b₁), (a₂, b₂) => by
        constructor
        · rintro (⟨_, _, hlt⟩ | ⟨_, hlt⟩)
          · constructor
            · exact left _ _ hlt
            · rintro ⟨⟩
              · apply lt_asymm hlt; assumption
              · exact lt_irrefl _ hlt
          · constructor
            · right
              rw [lt_iff_le_not_le] at hlt
              exact hlt.1
            · rintro ⟨⟩
              · apply lt_irrefl a₁
                assumption
              · rw [lt_iff_le_not_le] at hlt
                apply hlt.2
                assumption
        · rintro ⟨⟨⟩, h₂r⟩
          · left
            assumption
          · right
            rw [lt_iff_le_not_le]
            constructor
            · assumption
            · intro h
              apply h₂r
              right
              exact h }
#align prod.lex.preorder Prod.Lex.preorder

theorem monotone_fst [Preorder α] [LE β] (t c : α ×ₗ β) (h : t ≤ c) :
    (ofLex t).1 ≤ (ofLex c).1 := by
  cases (Prod.Lex.le_iff t c).mp h with
  | inl h' => exact h'.le
  | inr h' => exact h'.1.le

section Preorder

variable [PartialOrder α] [Preorder β]

theorem toLex_mono : Monotone (toLex : α × β → α ×ₗ β) := by
  rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ ⟨ha, hb⟩
  obtain rfl | ha : a₁ = a₂ ∨ _ := ha.eq_or_lt
  · exact right _ hb
  · exact left _ _ ha
#align prod.lex.to_lex_mono Prod.Lex.toLex_mono

theorem toLex_strictMono : StrictMono (toLex : α × β → α ×ₗ β) := by
  rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h
  obtain rfl | ha : a₁ = a₂ ∨ _ := h.le.1.eq_or_lt
  · exact right _ (Prod.mk_lt_mk_iff_right.1 h)
  · exact left _ _ ha
#align prod.lex.to_lex_strict_mono Prod.Lex.toLex_strictMono

end Preorder

/-- Dictionary / lexicographic partial order for pairs. -/
instance partialOrder (α β : Type*) [PartialOrder α] [PartialOrder β] : PartialOrder (α ×ₗ β) :=
  { Prod.Lex.preorder α β with
    le_antisymm := by
      haveI : IsStrictOrder α (· < ·) := { irrefl := lt_irrefl, trans := fun _ _ _ => lt_trans }
      haveI : IsAntisymm β (· ≤ ·) := ⟨fun _ _ => le_antisymm⟩
      exact @antisymm _ (Prod.Lex _ _) _ }
#align prod.lex.partial_order Prod.Lex.partialOrder

/-- Dictionary / lexicographic linear order for pairs. -/
instance linearOrder (α β : Type*) [LinearOrder α] [LinearOrder β] : LinearOrder (α ×ₗ β) :=
  { Prod.Lex.partialOrder α β with
    le_total := total_of (Prod.Lex _ _),
    decidableLE := Prod.Lex.decidable _ _,
    decidableLT := Prod.Lex.decidable _ _,
    decidableEq := Lex.decidableEq _ _, }
#align prod.lex.linear_order Prod.Lex.linearOrder

instance [Ord α] [Ord β] : Ord (α ×ₗ β) where
  compare := compareLex (compareOn (·.1)) (compareOn (·.2))

instance orderBot [PartialOrder α] [Preorder β] [OrderBot α] [OrderBot β] : OrderBot (α ×ₗ β) where
  bot := toLex ⊥
  bot_le _ := toLex_mono bot_le
#align prod.lex.order_bot Prod.Lex.orderBot

instance orderTop [PartialOrder α] [Preorder β] [OrderTop α] [OrderTop β] : OrderTop (α ×ₗ β) where
  top := toLex ⊤
  le_top _ := toLex_mono le_top
#align prod.lex.order_top Prod.Lex.orderTop

instance boundedOrder [PartialOrder α] [Preorder β] [BoundedOrder α] [BoundedOrder β] :
    BoundedOrder (α ×ₗ β) :=
  { Lex.orderBot, Lex.orderTop with }
#align prod.lex.bounded_order Prod.Lex.boundedOrder

instance [Preorder α] [Preorder β] [DenselyOrdered α] [DenselyOrdered β] :
    DenselyOrdered (α ×ₗ β) where
  dense := by
    rintro _ _ (@⟨a₁, b₁, a₂, b₂, h⟩ | @⟨a, b₁, b₂, h⟩)
    · obtain ⟨c, h₁, h₂⟩ := exists_between h
      exact ⟨(c, b₁), left _ _ h₁, left _ _ h₂⟩
    · obtain ⟨c, h₁, h₂⟩ := exists_between h
      exact ⟨(a, c), right _ h₁, right _ h₂⟩

instance noMaxOrder_of_left [Preorder α] [Preorder β] [NoMaxOrder α] : NoMaxOrder (α ×ₗ β) where
  exists_gt := by
    rintro ⟨a, b⟩
    obtain ⟨c, h⟩ := exists_gt a
    exact ⟨⟨c, b⟩, left _ _ h⟩
#align prod.lex.no_max_order_of_left Prod.Lex.noMaxOrder_of_left

instance noMinOrder_of_left [Preorder α] [Preorder β] [NoMinOrder α] : NoMinOrder (α ×ₗ β) where
  exists_lt := by
    rintro ⟨a, b⟩
    obtain ⟨c, h⟩ := exists_lt a
    exact ⟨⟨c, b⟩, left _ _ h⟩
#align prod.lex.no_min_order_of_left Prod.Lex.noMinOrder_of_left

instance noMaxOrder_of_right [Preorder α] [Preorder β] [NoMaxOrder β] : NoMaxOrder (α ×ₗ β) where
  exists_gt := by
    rintro ⟨a, b⟩
    obtain ⟨c, h⟩ := exists_gt b
    exact ⟨⟨a, c⟩, right _ h⟩
#align prod.lex.no_max_order_of_right Prod.Lex.noMaxOrder_of_right

instance noMinOrder_of_right [Preorder α] [Preorder β] [NoMinOrder β] : NoMinOrder (α ×ₗ β) where
  exists_lt := by
    rintro ⟨a, b⟩
    obtain ⟨c, h⟩ := exists_lt b
    exact ⟨⟨a, c⟩, right _ h⟩
#align prod.lex.no_min_order_of_right Prod.Lex.noMinOrder_of_right

end Prod.Lex
