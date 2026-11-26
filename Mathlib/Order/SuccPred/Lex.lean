/-
Copyright (c) 2026 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.Order.SuccPred.Basic
public import Mathlib.Order.Sum.Order
public import Mathlib.Order.Prod.Lex.Basic

/-!
# Instances for lexicographic sums and products

We prove `SuccOrder (α ⊕ₗ β)` and `SuccOrder (α ×ₗ β)` under different assumptions on `α` and `β`.
In particular, although we provide more than one instance for each, these have non-overlapping
typeclass assumptions, and should not lead to any diamonds.
-/

public section
variable {α β : Type*}

/-! ### Lexicographic sum -/

open Order

namespace Sum.Lex

section NoMaxOrder
variable [Preorder α] [SuccOrder α] [NoMaxOrder α]
  [Preorder β] [SuccOrder β]

instance : SuccOrder (α ⊕ₗ β) where
  succ x := (ofLex x).elim (fun a ↦ toLex (inl (succ a))) (fun b ↦ toLex (inr (succ b)))
  le_succ := by simp
  max_of_succ_le := by simp
  succ_le_of_lt := by simpa using fun _ _ ↦ succ_le_of_lt

@[simp]
theorem succ_inl (x : α) : succ (toLex (inl (β := β) x)) = toLex (inl (succ x)) :=
  rfl

@[simp]
theorem succ_inr (x : β) : succ (toLex (inr (α := α) x)) = toLex (inr (succ x)) :=
  rfl

end NoMaxOrder

section OrderTop
variable [PartialOrder α] [SuccOrder α] [OrderTop α]
  [Preorder β] [SuccOrder β] [OrderBot β] [DecidableEq α]

instance : SuccOrder (α ⊕ₗ β) where
  succ x := (ofLex x).elim
    (fun a ↦ toLex (if a = ⊤ then inr ⊥ else inl (succ a))) (fun b ↦ toLex (inr (succ b)))
  le_succ := by rw [Lex.forall]; aesop
  max_of_succ_le := by rw [Lex.forall]; aesop
  succ_le_of_lt := by simp_rw [Lex.forall]; aesop (add apply safe [succ_le_of_lt])

@[simp]
theorem succ_inl_of_ne_top {x : α} (hx : x ≠ ⊤) :
    succ (toLex (inl (β := β) x)) = toLex (inl (succ x)) :=
  ite_eq_right hx

@[simp]
theorem succ_inl_top : succ (toLex (inl ⊤ : α ⊕ β)) = toLex (inr ⊥) :=
  ite_eq_left rfl

@[simp]
theorem succ_inr' (x : β) : succ (toLex (inr (α := α) x)) = toLex (inr (succ x)) :=
  rfl

end OrderTop

section NoMinOrder
variable [Preorder α] [PredOrder α]
  [Preorder β] [PredOrder β] [NoMinOrder β]

instance : PredOrder (α ⊕ₗ β) where
  pred x := (ofLex x).elim (fun a ↦ toLex (inl (pred a))) (fun b ↦ toLex (inr (pred b)))
  pred_le := by simp
  min_of_le_pred := by simp
  le_pred_of_lt := by simpa using fun _ _ ↦ le_pred_of_lt

@[simp]
theorem pred_inl (x : α) : pred (toLex (inl (β := β) x)) = toLex (inl (pred x)) :=
  rfl

@[simp]
theorem pred_inr (x : β) : pred (toLex (inr (α := α) x)) = toLex (inr (pred x)) :=
  rfl

end NoMinOrder

section OrderBot
variable [Preorder α] [PredOrder α] [OrderTop α]
  [PartialOrder β] [PredOrder β] [OrderBot β] [DecidableEq β]

instance : PredOrder (α ⊕ₗ β) where
  pred x := (ofLex x).elim
    (fun a ↦ toLex (inl (pred a))) (fun b ↦ toLex (if b = ⊥ then inl ⊤ else inr (pred b)))
  pred_le := by rw [Lex.forall]; aesop
  min_of_le_pred := by rw [Lex.forall]; aesop
  le_pred_of_lt := by simp_rw [Lex.forall]; aesop (add apply safe [le_pred_of_lt])

@[simp]
theorem pred_inl' (x : α) : pred (toLex (inl (β := β) x)) = toLex (inl (pred x)) :=
  rfl

@[simp]
theorem pred_inr_of_ne_bot {x : β} (hx : x ≠ ⊥) :
    pred (toLex (inr (α := α) x)) = toLex (inr (pred x)) :=
  ite_eq_right hx

@[simp]
theorem pred_inr_bot : pred (toLex (inr ⊥ : α ⊕ β)) = toLex (inl ⊤) :=
  ite_eq_left rfl

end OrderBot
end Sum.Lex

namespace Prod.Lex



end Prod.Lex
