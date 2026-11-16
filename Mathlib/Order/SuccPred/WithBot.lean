/-
Copyright (c) 2024 Yaël Dillies, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Andrew Yang
-/
module

public import Mathlib.Order.SuccPred.Basic

set_option doc.verso true
set_option doc.verso.suggestions false

/-!
# Successor function on `WithBot`

This file defines the successor of `a : WithBot α` as an element of `α`, and dually for `WithTop`.
-/

@[expose] public section

variable {α : Type*} {x y : WithBot α}

namespace WithBot
section Preorder
variable [Preorder α] [OrderBot α] [SuccOrder α]

/-- The successor of `a : WithBot α` as an element of `α`. -/
@[to_dual
/-- The predecessor of `a : WithTop α` as an element of `α`. -/]
def succ (a : WithBot α) : α := a.recBotCoe ⊥ Order.succ

/-- Not to be confused with `WithBot.orderSucc_bot`, which is about `Order.succ`. -/
@[to_dual (attr := simp)
/-- Not to be confused with `WithTop.orderPred_top`, which is about `Order.pred`. -/]
lemma succ_bot : succ (⊥ : WithBot α) = ⊥ := rfl

/-- Not to be confused with `WithBot.orderSucc_coe`, which is about `Order.succ`. -/
@[to_dual (attr := simp)
/-- Not to be confused with `WithTop.orderPred_coe`, which is about `Order.pred`. -/]
lemma succ_coe (a : α) : succ (a : WithBot α) = Order.succ a := rfl

@[to_dual]
lemma succ_eq_succ : ∀ a : WithBot α, succ a = Order.succ a
  | ⊥ => rfl
  | (a : α) => rfl

@[to_dual pred_lt]
lemma lt_succ [NoMaxOrder α] (x : WithBot α) : x < x.succ :=
  succ_eq_succ x ▸ Order.lt_succ x

@[to_dual]
lemma succ_mono : Monotone (succ : WithBot α → α)
  | ⊥, _, _ => by simp
  | (a : α), ⊥, hab => by simp at hab
  | (a : α), (b : α), hab => Order.succ_le_succ (by simpa using hab)

@[to_dual]
lemma succ_strictMono [NoMaxOrder α] : StrictMono (succ : WithBot α → α)
  | ⊥, (b : α), hab => by simp
  | (a : α), (b : α), hab => Order.succ_lt_succ (by simpa using hab)

@[to_dual (attr := gcongr)]
lemma succ_le_succ (hxy : x ≤ y) : x.succ ≤ y.succ := succ_mono hxy
@[to_dual (attr := gcongr)]
lemma succ_lt_succ [NoMaxOrder α] (hxy : x < y) : x.succ < y.succ := succ_strictMono hxy

end Preorder

section PartialOrder
variable [PartialOrder α] [OrderBot α] [PredOrder α]
  [∀ a : α, Decidable (Order.pred a = a)]

@[to_dual (attr := simp)]
theorem succ_pred_coe [SuccOrder α] (a : α) : succ (Order.pred (a : WithBot α)) = a := by
  by_cases ha : IsMin a
  · rw [pred_coe_of_isMin ha, succ_bot, ha.eq_bot]
  · rw [pred_coe_of_not_isMin ha, succ_coe, Order.succ_pred_of_not_isMin ha]

end PartialOrder

section LinearOrder
variable [Nontrivial α] [LinearOrder α] [OrderBot α] [SuccOrder α]

@[to_dual (attr := simp)]
theorem succ_eq_bot (a : WithBot α) : succ a = ⊥ ↔ a = ⊥ := by
  cases a
  · simp
  · simpa [succ_coe, coe_ne_bot, iff_false] using Order.succ_ne_bot _

end LinearOrder
end WithBot
