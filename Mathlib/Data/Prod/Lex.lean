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

-- porting note: `Prod.Lex` is not protected in core, hence the `_root_.` prefix
-- This will be fixed in nightly-2022-11-30
@[inherit_doc] notation:35 α " ×ₗ " β:34 => _root_.Lex (Prod α β)

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
        -- ⊢ (a₁, b₁) < (a₂, b₂) → (a₁, b₁) ≤ (a₂, b₂) ∧ ¬(a₂, b₂) ≤ (a₁, b₁)
        · rintro (⟨_, _, hlt⟩ | ⟨_, hlt⟩)
          -- ⊢ (a₁, b₁) ≤ (a₂, b₂) ∧ ¬(a₂, b₂) ≤ (a₁, b₁)
          · constructor
            -- ⊢ (a₁, b₁) ≤ (a₂, b₂)
            · exact left _ _ hlt
              -- 🎉 no goals
            · rintro ⟨⟩
              -- ⊢ False
              · apply lt_asymm hlt; assumption
                -- ⊢ a₂ < a₁
                                    -- 🎉 no goals
              · exact lt_irrefl _ hlt
                -- 🎉 no goals
          · constructor
            -- ⊢ (a₁, b₁) ≤ (a₁, b₂)
            · right
              -- ⊢ b₁ ≤ b₂
              rw [lt_iff_le_not_le] at hlt
              -- ⊢ b₁ ≤ b₂
              exact hlt.1
              -- 🎉 no goals
            · rintro ⟨⟩
              -- ⊢ False
              · apply lt_irrefl a₁
                -- ⊢ a₁ < a₁
                assumption
                -- 🎉 no goals
              · rw [lt_iff_le_not_le] at hlt
                -- ⊢ False
                apply hlt.2
                -- ⊢ b₂ ≤ b₁
                assumption
                -- 🎉 no goals
        · rintro ⟨⟨⟩, h₂r⟩
          -- ⊢ (a₁, b₁) < (a₂, b₂)
          · left
            -- ⊢ a₁ < a₂
            assumption
            -- 🎉 no goals
          · right
            -- ⊢ b₁ < b₂
            rw [lt_iff_le_not_le]
            -- ⊢ b₁ ≤ b₂ ∧ ¬b₂ ≤ b₁
            constructor
            -- ⊢ b₁ ≤ b₂
            · assumption
              -- 🎉 no goals
            · intro h
              -- ⊢ False
              apply h₂r
              -- ⊢ (a₁, b₂) ≤ (a₁, b₁)
              right
              -- ⊢ b₂ ≤ b₁
              exact h }
              -- 🎉 no goals
#align prod.lex.preorder Prod.Lex.preorder

section Preorder

variable [PartialOrder α] [Preorder β]

-- porting note: type class search sees right through the type synonrm for `α ×ₗ β` and uses the
-- `Preorder` structure for `α × β` instead
-- This is hopefully the same problems as in https://github.com/leanprover/lean4/issues/1891
-- and will be fixed in nightly-2022-11-30
theorem toLex_mono : @Monotone _ _ _ (Prod.Lex.preorder α β) (toLex : α × β → α ×ₗ β) := by
  rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ ⟨ha, hb⟩
  -- ⊢ ↑toLex (a₁, b₁) ≤ ↑toLex (a₂, b₂)
  obtain rfl | ha : a₁ = a₂ ∨ _ := ha.eq_or_lt
  -- ⊢ ↑toLex (a₁, b₁) ≤ ↑toLex (a₁, b₂)
  · exact right _ hb
    -- 🎉 no goals
  · exact left _ _ ha
    -- 🎉 no goals
#align prod.lex.to_lex_mono Prod.Lex.toLex_mono

-- porting note: type class search sees right through the type synonrm for `α ×ₗ β` and uses the
-- `Preorder` structure for `α × β` instead
-- This is hopefully the same problems as in https://github.com/leanprover/lean4/issues/1891
-- and will be fixed in nightly-2022-11-30
theorem toLex_strictMono : @StrictMono _ _ _ (Prod.Lex.preorder α β) (toLex : α × β → α ×ₗ β) := by
  rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h
  -- ⊢ ↑toLex (a₁, b₁) < ↑toLex (a₂, b₂)
  obtain rfl | ha : a₁ = a₂ ∨ _ := h.le.1.eq_or_lt
  -- ⊢ ↑toLex (a₁, b₁) < ↑toLex (a₁, b₂)
  · exact right _ (Prod.mk_lt_mk_iff_right.1 h)
    -- 🎉 no goals
  · exact left _ _ ha
    -- 🎉 no goals
#align prod.lex.to_lex_strict_mono Prod.Lex.toLex_strictMono

end Preorder

/-- Dictionary / lexicographic partial order for pairs. -/
instance partialOrder (α β : Type*) [PartialOrder α] [PartialOrder β] : PartialOrder (α ×ₗ β) :=
  { Prod.Lex.preorder α β with
    le_antisymm := by
      haveI : IsStrictOrder α (· < ·) := { irrefl := lt_irrefl, trans := fun _ _ _ => lt_trans }
      -- ⊢ ∀ (a b : Lex (α × β)), a ≤ b → b ≤ a → a = b
      haveI : IsAntisymm β (· ≤ ·) := ⟨fun _ _ => le_antisymm⟩
      -- ⊢ ∀ (a b : Lex (α × β)), a ≤ b → b ≤ a → a = b
      exact @antisymm _ (Prod.Lex _ _) _ }
      -- 🎉 no goals
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
    -- ⊢ ∃ a, (a₁, b₁) < a ∧ a < (a₂, b₂)
    · obtain ⟨c, h₁, h₂⟩ := exists_between h
      -- ⊢ ∃ a, (a₁, b₁) < a ∧ a < (a₂, b₂)
      exact ⟨(c, b₁), left _ _ h₁, left _ _ h₂⟩
      -- 🎉 no goals
    · obtain ⟨c, h₁, h₂⟩ := exists_between h
      -- ⊢ ∃ a_1, (a, b₁) < a_1 ∧ a_1 < (a, b₂)
      exact ⟨(a, c), right _ h₁, right _ h₂⟩
      -- 🎉 no goals

instance noMaxOrder_of_left [Preorder α] [Preorder β] [NoMaxOrder α] : NoMaxOrder (α ×ₗ β) where
  exists_gt := by
    rintro ⟨a, b⟩
    -- ⊢ ∃ b_1, (a, b) < b_1
    obtain ⟨c, h⟩ := exists_gt a
    -- ⊢ ∃ b_1, (a, b) < b_1
    exact ⟨⟨c, b⟩, left _ _ h⟩
    -- 🎉 no goals
#align prod.lex.no_max_order_of_left Prod.Lex.noMaxOrder_of_left

instance noMinOrder_of_left [Preorder α] [Preorder β] [NoMinOrder α] : NoMinOrder (α ×ₗ β) where
  exists_lt := by
    rintro ⟨a, b⟩
    -- ⊢ ∃ b_1, b_1 < (a, b)
    obtain ⟨c, h⟩ := exists_lt a
    -- ⊢ ∃ b_1, b_1 < (a, b)
    exact ⟨⟨c, b⟩, left _ _ h⟩
    -- 🎉 no goals
#align prod.lex.no_min_order_of_left Prod.Lex.noMinOrder_of_left

instance noMaxOrder_of_right [Preorder α] [Preorder β] [NoMaxOrder β] : NoMaxOrder (α ×ₗ β) where
  exists_gt := by
    rintro ⟨a, b⟩
    -- ⊢ ∃ b_1, (a, b) < b_1
    obtain ⟨c, h⟩ := exists_gt b
    -- ⊢ ∃ b_1, (a, b) < b_1
    exact ⟨⟨a, c⟩, right _ h⟩
    -- 🎉 no goals
#align prod.lex.no_max_order_of_right Prod.Lex.noMaxOrder_of_right

instance noMinOrder_of_right [Preorder α] [Preorder β] [NoMinOrder β] : NoMinOrder (α ×ₗ β) where
  exists_lt := by
    rintro ⟨a, b⟩
    -- ⊢ ∃ b_1, b_1 < (a, b)
    obtain ⟨c, h⟩ := exists_lt b
    -- ⊢ ∃ b_1, b_1 < (a, b)
    exact ⟨⟨a, c⟩, right _ h⟩
    -- 🎉 no goals
#align prod.lex.no_min_order_of_right Prod.Lex.noMinOrder_of_right

end Prod.Lex
