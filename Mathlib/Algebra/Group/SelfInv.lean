/-
Copyright (c) 2026 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
module

public import Mathlib.Algebra.Group.Basic

/-!
# Self-inverse elements

This file defines self-inverse elements of a type with an inversion, i.e. elements `a` satisfying
`a⁻¹ = a`.

## Main declarations

* `IsSelfInv a`: The element `a` satisfies `a⁻¹ = a`.
* `IsSelfNeg a`: The element `a` satisfies `-a = a`.
-/

@[expose] public section

variable {α : Type*}

section Inv

variable [Inv α] {a : α}

/-- An element `a` is *self-inverse* if `a⁻¹ = a`. -/
@[to_additive /-- An element `a` is *self-negative* if `-a = a`. -/]
def IsSelfInv (a : α) : Prop := a⁻¹ = a

@[to_additive]
lemma isSelfInv_iff : IsSelfInv a ↔ a⁻¹ = a := Iff.rfl

@[to_additive]
protected lemma IsSelfInv.inv_eq (h : IsSelfInv a) : a⁻¹ = a := h

@[to_additive]
protected lemma IsSelfInv.eq_inv (h : IsSelfInv a) : a = a⁻¹ := h.symm

end Inv

@[to_additive (attr := simp)]
protected lemma IsSelfInv.one [InvOneClass α] : IsSelfInv (1 : α) := inv_one

@[to_additive (attr := simp)]
lemma isSelfInv_inv [InvolutiveInv α] {a : α} : IsSelfInv a⁻¹ ↔ IsSelfInv a := by
  rw [isSelfInv_iff, isSelfInv_iff, inv_inv, eq_comm]

@[to_additive]
alias ⟨_, IsSelfInv.inv⟩ := isSelfInv_inv

@[to_additive]
protected lemma IsSelfInv.conj [DivisionMonoid α] {a b : α} (h : IsSelfInv a) :
    IsSelfInv (b * a * b⁻¹) := by
  rw [isSelfInv_iff, mul_inv_rev, mul_inv_rev, inv_inv, h, mul_assoc]

section DivisionCommMonoid

variable [DivisionCommMonoid α] {a b : α}

@[to_additive]
protected lemma IsSelfInv.mul (ha : IsSelfInv a) (hb : IsSelfInv b) : IsSelfInv (a * b) := by
  rw [isSelfInv_iff, mul_inv, ha, hb]

@[to_additive]
protected lemma IsSelfInv.div (ha : IsSelfInv a) (hb : IsSelfInv b) : IsSelfInv (a / b) :=
  div_eq_mul_inv a b ▸ ha.mul hb.inv

end DivisionCommMonoid
