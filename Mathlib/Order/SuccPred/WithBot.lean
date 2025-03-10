/-
Copyright (c) 2024 Yaël Dillies, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Andrew Yang
-/
import Mathlib.Order.SuccPred.Basic

/-!
# Successor function on `WithBot`

This file defines the successor of `a : WithBot α` as an element of `α`, and dually for `WithTop`.
-/

namespace WithBot
variable {α : Type*} [Preorder α] [OrderBot α] [SuccOrder α] {x y : WithBot α}

/-- The successor of `a : WithBot α` as an element of `α`. -/
def succ (a : WithBot α) : α := a.recBotCoe ⊥ Order.succ

/-- Not to be confused with `WithBot.orderSucc_bot`, which is about `Order.succ`. -/
@[simp] lemma succ_bot : succ (⊥ : WithBot α) = ⊥ := rfl

/-- Not to be confused with `WithBot.orderSucc_coe`, which is about `Order.succ`. -/
@[simp] lemma succ_coe (a : α) : succ (a : WithBot α) = Order.succ a := rfl

lemma succ_eq_succ : ∀ a : WithBot α, succ a = Order.succ a
  | ⊥ => rfl
  | (a : α) => rfl

lemma succ_mono : Monotone (succ : WithBot α → α)
  | ⊥, _, _ => by simp
  | (a : α), ⊥, hab => by simp at hab
  | (a : α), (b : α), hab => Order.succ_le_succ (by simpa using hab)

lemma succ_strictMono [NoMaxOrder α] : StrictMono (succ : WithBot α → α)
  | ⊥, (b : α), hab => by simp
  | (a : α), (b : α), hab => Order.succ_lt_succ (by simpa using hab)

@[gcongr] lemma succ_le_succ (hxy : x ≤ y) : x.succ ≤ y.succ := succ_mono hxy
@[gcongr] lemma succ_lt_succ [NoMaxOrder α] (hxy : x < y) : x.succ < y.succ := succ_strictMono hxy

section LinearOrder

variable {α : Type*} [Nontrivial α] [LinearOrder α] [OrderBot α] [SuccOrder α]

@[simp]
theorem succ_eq_bot (a : WithBot α) : WithBot.succ a = ⊥ ↔ a = ⊥ := by
  cases a
  · simp
  · simp only [WithBot.succ_coe, WithBot.coe_ne_bot, iff_false]
    apply ne_of_gt
    by_contra! h
    have h₂ : _ = ⊥ := le_bot_iff.mp ((Order.le_succ _).trans h)
    exact not_isMax_bot (h₂ ▸ Order.max_of_succ_le (h.trans bot_le))

end LinearOrder
end WithBot

namespace WithTop
variable {α : Type*} [Preorder α] [OrderTop α] [PredOrder α] {x y : WithTop α}

/-- The predecessor of `a : WithTop α` as an element of `α`. -/
def pred (a : WithTop α) : α := a.recTopCoe ⊤ Order.pred

/-- Not to be confused with `WithTop.orderPred_top`, which is about `Order.pred`. -/
@[simp] lemma pred_top : pred (⊤ : WithTop α) = ⊤ := rfl

/-- Not to be confused with `WithTop.orderPred_coe`, which is about `Order.pred`. -/
@[simp] lemma pred_coe (a : α) : pred (a : WithTop α) = Order.pred a := rfl

lemma pred_eq_pred : ∀ a : WithTop α, pred a = Order.pred a
  | ⊤ => rfl
  | (a : α) => rfl

lemma pred_mono : Monotone (pred : WithTop α → α)
  | _, ⊤, _ => by simp
  | ⊤, (a : α), hab => by simp at hab
  | (a : α), (b : α), hab => Order.pred_le_pred (by simpa using hab)

lemma pred_strictMono [NoMinOrder α] : StrictMono (pred : WithTop α → α)
  | (b : α), ⊤, hab => by simp
  | (a : α), (b : α), hab => Order.pred_lt_pred (by simpa using hab)

@[gcongr] lemma pred_le_pred (hxy : x ≤ y) : x.pred ≤ y.pred := pred_mono hxy
@[gcongr] lemma pred_lt_pred [NoMinOrder α] (hxy : x < y) : x.pred < y.pred := pred_strictMono hxy

section LinearOrder

variable {α : Type*} [Nontrivial α] [LinearOrder α] [OrderTop α] [PredOrder α]

@[simp]
theorem pred_eq_top (a : WithTop α) : WithTop.pred a = ⊤ ↔ a = ⊤ := by
  cases a
  · simp
  · simp only [WithTop.pred_coe, WithTop.coe_ne_top, iff_false]
    apply ne_of_lt
    by_contra! h
    have h₂ : _ = ⊤ := top_le_iff.mp (h.trans (Order.pred_le _))
    exact not_isMin_top (h₂ ▸ Order.min_of_le_pred (le_top.trans h))

end LinearOrder
end WithTop
