/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
module

public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags
public import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop

/-!
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
  toFun
  | 0 => Multiplicative.ofAdd ⊥
  | .some x => Multiplicative.ofAdd (x.toAdd : WithBot α)
  invFun x := match x.toAdd with
  | .bot => 0
  | .some x => (Multiplicative.ofAdd (α := α) x : WithZero (Multiplicative α))
  left_inv x := by cases x <;> simp
  right_inv x := by
    match h : x.toAdd with
    | .bot =>
      simp [h]
      simp at h
      simp [← h]
    | .some x =>
      simp [h]
      simp [← h]
  map_mul' x y := by
    cases x <;> cases y <;> simp [← ofAdd_add, ← WithZero.coe_mul]

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
  cases x <;> cases y <;> simp [toMulBot]

@[simp]
theorem toMulBot_le : toMulBot a ≤ toMulBot b ↔ a ≤ b :=
  by cases a <;> cases b <;> simp [toMulBot]

@[simp]
theorem toMulBot_lt : toMulBot a < toMulBot b ↔ a < b :=
  by cases a <;> cases b <;> simp [toMulBot]

end WithZero
