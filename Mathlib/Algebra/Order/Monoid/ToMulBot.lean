/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
module

public import Mathlib.Algebra.Order.GroupWithZero.Canonical

set_option doc.verso true
set_option doc.verso.suggestions false

/-!
# `WithZero (Multiplicative α)` is equivalent to `Multiplicative (WithBot α)`

Making an additive monoid multiplicative then adding a zero is the same as adding a bottom
element then making it multiplicative.
-/

@[expose] public section


universe u

variable {α : Type u}

namespace WithZero

variable [Add α]

/-- Making an additive monoid multiplicative then adding a zero is the same as adding a bottom
element then making it multiplicative. -/
def toMulBot : WithZero (Multiplicative α) ≃* Multiplicative (WithBot α) where
  toFun | 0 => .ofAdd ⊥ | (x : Multiplicative α) => .ofAdd (Multiplicative.toAdd x : α)
  invFun x := match x.toAdd with
    | ⊥ => 0
    | (x : α) => (.ofAdd x : Multiplicative α)
  map_mul' x y := by cases x <;> cases y <;> simp [← ofAdd_add, ← coe_mul]
  left_inv x := by cases x <;> simp
  right_inv x := by cases x with | ofAdd x => cases x <;> simp

@[simp]
theorem toMulBot_zero : toMulBot (0 : WithZero (Multiplicative α)) = Multiplicative.ofAdd ⊥ :=
  rfl

@[simp]
theorem toMulBot_coe (x : Multiplicative α) :
    toMulBot ↑x = Multiplicative.ofAdd (↑x.toAdd : WithBot α) :=
  rfl

@[simp]
theorem toMulBot_symm_bot : toMulBot.symm (Multiplicative.ofAdd (⊥ : WithBot α)) = 0 :=
  rfl

@[simp]
theorem toMulBot_coe_ofAdd (x : α) :
    toMulBot.symm (Multiplicative.ofAdd (x : WithBot α)) = Multiplicative.ofAdd x :=
  rfl

variable [Preorder α] (a b : WithZero (Multiplicative α))

theorem toMulBot_strictMono : StrictMono (@toMulBot α _) := fun x y => by
  cases x with
  | zero =>
    cases y with
      | zero => simp
      | coe y => cases y with | ofAdd y => simp only [zero_lt_coe, toMulBot_zero, toMulBot_coe,
          toAdd_ofAdd, Multiplicative.ofAdd_lt, WithBot.bot_lt_coe, imp_self]
  | coe x =>
    cases x with
    | ofAdd x =>
      cases y with
      | zero => simp
      | coe y => cases y with | ofAdd y => simp

@[simp]
theorem toMulBot_le : toMulBot a ≤ toMulBot b ↔ a ≤ b := by
  cases a with
  | zero => simp
  | coe a =>
    cases a with
    | ofAdd a =>
      cases b with
      | zero => simp only [toMulBot_coe, toAdd_ofAdd, toMulBot_zero, Multiplicative.ofAdd_le,
          WithBot.le_bot_iff, WithBot.coe_ne_bot, WithZero.nonpos_iff_eq_zero, coe_ne_zero]
      | coe b => cases b; simp

@[simp]
theorem toMulBot_lt : toMulBot a < toMulBot b ↔ a < b := by
  cases a with
  | zero =>
    cases b with
    | zero => simp
    | coe b => simp only [toMulBot_zero, toMulBot_coe, Multiplicative.ofAdd_lt, WithBot.bot_lt_coe,
        zero_lt_coe]
  | coe a =>
    cases a with
    | ofAdd a =>
      cases b with
      | zero => simp
      | coe b => cases b; simp

end WithZero
