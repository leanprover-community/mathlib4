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
protected alias ⟨IsSelfInv.inv_eq, IsSelfInv.of_inv_eq⟩ := isSelfInv_iff

@[to_additive]
protected lemma IsSelfInv.eq_inv (h : IsSelfInv a) : a = a⁻¹ := h.symm

@[to_additive]
instance [DecidableEq α] : Decidable (IsSelfInv a) := decidable_of_iff _ isSelfInv_iff.symm

end Inv

@[to_additive (attr := simp)]
protected lemma IsSelfInv.one [InvOneClass α] : IsSelfInv (1 : α) := inv_one

@[to_additive (attr := simp)]
lemma isSelfInv_inv [InvolutiveInv α] {a : α} : IsSelfInv a⁻¹ ↔ IsSelfInv a := by
  rw [isSelfInv_iff, isSelfInv_iff, inv_inv, eq_comm]

@[to_additive]
protected alias ⟨_, IsSelfInv.inv⟩ := isSelfInv_inv

@[to_additive]
protected lemma IsSelfInv.conj [DivisionMonoid α] {a : α} (h : IsSelfInv a) (b : α) :
    IsSelfInv (b * a * b⁻¹) := by
  rw [isSelfInv_iff, mul_inv_rev, mul_inv_rev, inv_inv, h, mul_assoc]

@[to_additive]
lemma isSelfInv_conj_iff [Group α] {a b : α} : IsSelfInv (b * a * b⁻¹) ↔ IsSelfInv a :=
  ⟨fun h ↦ by simpa [mul_assoc] using h.conj b⁻¹, fun h ↦ h.conj b⟩

@[to_additive]
protected lemma IsSelfInv.pow [DivisionMonoid α] {a : α} (h : IsSelfInv a) (n : ℕ) :
    IsSelfInv (a ^ n) := by
  rw [isSelfInv_iff, ← inv_pow, h.inv_eq]

@[to_additive]
protected lemma IsSelfInv.zpow [DivisionMonoid α] {a : α} (h : IsSelfInv a) (n : ℤ) :
    IsSelfInv (a ^ n) := by
  rw [isSelfInv_iff, ← inv_zpow, h.inv_eq]

@[to_additive isSelfNeg_iff_two_nsmul_eq_zero]
lemma isSelfInv_iff_sq_eq_one [Group α] {a : α} : IsSelfInv a ↔ a ^ 2 = 1 := by
  rw [isSelfInv_iff, sq, inv_eq_iff_mul_eq_one]

section DivisionCommMonoid

variable [DivisionCommMonoid α] {a b : α}

@[to_additive]
protected lemma IsSelfInv.mul (ha : IsSelfInv a) (hb : IsSelfInv b) : IsSelfInv (a * b) := by
  rw [isSelfInv_iff, mul_inv, ha, hb]

@[to_additive]
protected lemma IsSelfInv.div (ha : IsSelfInv a) (hb : IsSelfInv b) : IsSelfInv (a / b) :=
  div_eq_mul_inv a b ▸ ha.mul hb.inv

end DivisionCommMonoid
