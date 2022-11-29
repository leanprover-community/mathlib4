/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Minchao Wu
-/
import Mathbin.Order.BoundedOrder

/-!
# Lexicographic order

This file defines the lexicographic relation for pairs of orders, partial orders and linear orders.

## Main declarations

* `prod.lex.<pre/partial_/linear_>order`: Instances lifting the orders on `α` and `β` to `α ×ₗ β`.

## Notation

* `α ×ₗ β`: `α × β` equipped with the lexicographic order

## See also

Related files are:
* `data.finset.colex`: Colexicographic order on finite sets.
* `data.list.lex`: Lexicographic order on lists.
* `data.pi.lex`: Lexicographic order on `Πₗ i, α i`.
* `data.psigma.order`: Lexicographic order on `Σ' i, α i`.
* `data.sigma.order`: Lexicographic order on `Σ i, α i`.
-/


variable {α β γ : Type _}

namespace Prod.Lex

-- mathport name: «expr ×ₗ »
notation:35 α " ×ₗ " β:34 => Lex (Prod α β)

unsafe instance [has_to_format α] [has_to_format β] : has_to_format (α ×ₗ β) :=
  prod.has_to_format

instance decidableEq (α β : Type _) [DecidableEq α] [DecidableEq β] : DecidableEq (α ×ₗ β) :=
  Prod.decidableEq
#align prod.lex.decidable_eq Prod.Lex.decidableEq

instance inhabited (α β : Type _) [Inhabited α] [Inhabited β] : Inhabited (α ×ₗ β) :=
  Prod.inhabited
#align prod.lex.inhabited Prod.Lex.inhabited

/-- Dictionary / lexicographic ordering on pairs.  -/
instance hasLe (α β : Type _) [LT α] [LE β] : LE (α ×ₗ β) where le := Prod.Lex (· < ·) (· ≤ ·)
#align prod.lex.has_le Prod.Lex.hasLe

instance hasLt (α β : Type _) [LT α] [LT β] : LT (α ×ₗ β) where lt := Prod.Lex (· < ·) (· < ·)
#align prod.lex.has_lt Prod.Lex.hasLt

theorem le_iff [LT α] [LE β] (a b : α × β) : toLex a ≤ toLex b ↔ a.1 < b.1 ∨ a.1 = b.1 ∧ a.2 ≤ b.2 :=
  Prod.lex_def (· < ·) (· ≤ ·)
#align prod.lex.le_iff Prod.Lex.le_iff

theorem lt_iff [LT α] [LT β] (a b : α × β) : toLex a < toLex b ↔ a.1 < b.1 ∨ a.1 = b.1 ∧ a.2 < b.2 :=
  Prod.lex_def (· < ·) (· < ·)
#align prod.lex.lt_iff Prod.Lex.lt_iff

/-- Dictionary / lexicographic preorder for pairs. -/
instance preorder (α β : Type _) [Preorder α] [Preorder β] : Preorder (α ×ₗ β) :=
  { Prod.Lex.hasLe α β, Prod.Lex.hasLt α β with le_refl := refl_of <| Prod.Lex _ _,
    le_trans := fun _ _ _ => trans_of <| Prod.Lex _ _,
    lt_iff_le_not_le := fun x₁ x₂ =>
      match x₁, x₂ with
      | toLex (a₁, b₁), toLex (a₂, b₂) => by
        constructor
        · rintro (⟨_, _, hlt⟩ | ⟨_, hlt⟩)
          · constructor
            · left
              assumption
              
            · rintro ⟨⟩
              · apply lt_asymm hlt
                assumption
                
              · apply lt_irrefl _ hlt
                
              
            
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
              exact h
              
            
           }
#align prod.lex.preorder Prod.Lex.preorder

section Preorder

variable [PartialOrder α] [Preorder β]

theorem to_lex_mono : Monotone (toLex : α × β → α ×ₗ β) := by
  rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ ⟨ha, hb⟩
  obtain rfl | ha : a₁ = a₂ ∨ _ := ha.eq_or_lt
  · exact right _ hb
    
  · exact left _ _ ha
    
#align prod.lex.to_lex_mono Prod.Lex.to_lex_mono

theorem to_lex_strict_mono : StrictMono (toLex : α × β → α ×ₗ β) := by
  rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h
  obtain rfl | ha : a₁ = a₂ ∨ _ := h.le.1.eq_or_lt
  · exact right _ (Prod.mk_lt_mk_iff_right.1 h)
    
  · exact left _ _ ha
    
#align prod.lex.to_lex_strict_mono Prod.Lex.to_lex_strict_mono

end Preorder

/-- Dictionary / lexicographic partial_order for pairs. -/
instance partialOrder (α β : Type _) [PartialOrder α] [PartialOrder β] : PartialOrder (α ×ₗ β) :=
  { Prod.Lex.preorder α β with
    le_antisymm := by
      haveI : IsStrictOrder α (· < ·) := { irrefl := lt_irrefl, trans := fun _ _ _ => lt_trans }
      haveI : IsAntisymm β (· ≤ ·) := ⟨fun _ _ => le_antisymm⟩
      exact @antisymm _ (Prod.Lex _ _) _ }
#align prod.lex.partial_order Prod.Lex.partialOrder

/-- Dictionary / lexicographic linear_order for pairs. -/
instance linearOrder (α β : Type _) [LinearOrder α] [LinearOrder β] : LinearOrder (α ×ₗ β) :=
  { Prod.Lex.partialOrder α β with le_total := total_of (Prod.Lex _ _), decidableLe := Prod.Lex.decidable _ _,
    decidableLt := Prod.Lex.decidable _ _, DecidableEq := Lex.decidableEq _ _ }
#align prod.lex.linear_order Prod.Lex.linearOrder

instance orderBot [PartialOrder α] [Preorder β] [OrderBot α] [OrderBot β] : OrderBot (α ×ₗ β) where
  bot := toLex ⊥
  bot_le a := to_lex_mono bot_le
#align prod.lex.order_bot Prod.Lex.orderBot

instance orderTop [PartialOrder α] [Preorder β] [OrderTop α] [OrderTop β] : OrderTop (α ×ₗ β) where
  top := toLex ⊤
  le_top a := to_lex_mono le_top
#align prod.lex.order_top Prod.Lex.orderTop

instance boundedOrder [PartialOrder α] [Preorder β] [BoundedOrder α] [BoundedOrder β] : BoundedOrder (α ×ₗ β) :=
  { Lex.orderBot, Lex.orderTop with }
#align prod.lex.bounded_order Prod.Lex.boundedOrder

instance [Preorder α] [Preorder β] [DenselyOrdered α] [DenselyOrdered β] : DenselyOrdered (α ×ₗ β) :=
  ⟨by
    rintro _ _ (@⟨a₁, b₁, a₂, b₂, h⟩ | @⟨a, b₁, b₂, h⟩)
    · obtain ⟨c, h₁, h₂⟩ := exists_between h
      exact ⟨(c, b₁), left _ _ h₁, left _ _ h₂⟩
      
    · obtain ⟨c, h₁, h₂⟩ := exists_between h
      exact ⟨(a, c), right _ h₁, right _ h₂⟩
      ⟩

instance no_max_order_of_left [Preorder α] [Preorder β] [NoMaxOrder α] : NoMaxOrder (α ×ₗ β) :=
  ⟨by
    rintro ⟨a, b⟩
    obtain ⟨c, h⟩ := exists_gt a
    exact ⟨⟨c, b⟩, left _ _ h⟩⟩
#align prod.lex.no_max_order_of_left Prod.Lex.no_max_order_of_left

instance no_min_order_of_left [Preorder α] [Preorder β] [NoMinOrder α] : NoMinOrder (α ×ₗ β) :=
  ⟨by
    rintro ⟨a, b⟩
    obtain ⟨c, h⟩ := exists_lt a
    exact ⟨⟨c, b⟩, left _ _ h⟩⟩
#align prod.lex.no_min_order_of_left Prod.Lex.no_min_order_of_left

instance no_max_order_of_right [Preorder α] [Preorder β] [NoMaxOrder β] : NoMaxOrder (α ×ₗ β) :=
  ⟨by
    rintro ⟨a, b⟩
    obtain ⟨c, h⟩ := exists_gt b
    exact ⟨⟨a, c⟩, right _ h⟩⟩
#align prod.lex.no_max_order_of_right Prod.Lex.no_max_order_of_right

instance no_min_order_of_right [Preorder α] [Preorder β] [NoMinOrder β] : NoMinOrder (α ×ₗ β) :=
  ⟨by
    rintro ⟨a, b⟩
    obtain ⟨c, h⟩ := exists_lt b
    exact ⟨⟨a, c⟩, right _ h⟩⟩
#align prod.lex.no_min_order_of_right Prod.Lex.no_min_order_of_right

end Prod.Lex

