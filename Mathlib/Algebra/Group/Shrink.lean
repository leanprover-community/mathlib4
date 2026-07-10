/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Group.Action.TransferInstance
public import Mathlib.Logic.Small.Defs

/-!
# Transfer group structures from `α` to `Shrink α`
-/

@[expose] public section

universe v
variable {M α : Type*} [Small.{v} α]

namespace Shrink

@[to_additive] noncomputable instance [One α] : One (Shrink.{v} α) := (equivShrink α).symm.one
@[to_additive] noncomputable instance [Mul α] : Mul (Shrink.{v} α) := (equivShrink α).symm.mul
@[to_additive] noncomputable instance [Div α] : Div (Shrink.{v} α) := (equivShrink α).symm.div
@[to_additive] noncomputable instance [Inv α] : Inv (Shrink.{v} α) := (equivShrink α).symm.Inv
@[to_additive] noncomputable instance [Pow α M] : Pow (Shrink.{v} α) M := (equivShrink α).symm.pow M

end Shrink

@[to_additive (attr := simp)]
lemma equivShrink_symm_one [One α] : (equivShrink α).symm 1 = 1 :=
  (equivShrink α).symm_apply_apply 1

@[to_additive (attr := simp)]
lemma equivShrink_symm_mul [Mul α] (x y : Shrink α) :
    (equivShrink α).symm (x * y) = (equivShrink α).symm x * (equivShrink α).symm y := by
  simp [Equiv.mul_def]

@[to_additive (attr := simp)]
lemma equivShrink_mul [Mul α] (x y : α) :
    equivShrink α (x * y) = equivShrink α x * equivShrink α y := by
  simp [Equiv.mul_def]

@[simp]
lemma equivShrink_symm_smul {M : Type*} [SMul M α] (m : M) (x : Shrink α) :
    (equivShrink α).symm (m • x) = m • (equivShrink α).symm x := by
  simp [Equiv.smul_def]

@[simp]
lemma equivShrink_smul {M : Type*} [SMul M α] (m : M) (x : α) :
    equivShrink α (m • x) = m • equivShrink α x := by
  simp [Equiv.smul_def]
@[to_additive (attr := simp)]
lemma equivShrink_symm_div [Div α] (x y : Shrink α) :
    (equivShrink α).symm (x / y) = (equivShrink α).symm x / (equivShrink α).symm y := by
  simp [Equiv.div_def]

@[to_additive (attr := simp)]
lemma equivShrink_div [Div α] (x y : α) :
    equivShrink α (x / y) = equivShrink α x / equivShrink α y := by
  simp [Equiv.div_def]

@[to_additive (attr := simp)]
lemma equivShrink_symm_inv [Inv α] (x : Shrink α) :
    (equivShrink α).symm x⁻¹ = ((equivShrink α).symm x)⁻¹ := by
  simp [Equiv.inv_def]

@[to_additive (attr := simp)]
lemma equivShrink_inv [Inv α] (x : α) : equivShrink α x⁻¹ = (equivShrink α x)⁻¹ := by
  simp [Equiv.inv_def]

namespace Shrink

/-- Shrink `α` to a smaller universe preserves multiplication. -/
@[to_additive /-- Shrink `α` to a smaller universe preserves addition. -/]
noncomputable def mulEquiv [Mul α] : Shrink.{v} α ≃* α := (equivShrink α).symm.mulEquiv

@[to_additive]
noncomputable instance [Semigroup α] : Semigroup (Shrink.{v} α) := (equivShrink α).symm.semigroup

@[to_additive]
noncomputable
instance [CommSemigroup α] : CommSemigroup (Shrink.{v} α) := (equivShrink α).symm.commSemigroup

@[to_additive]
instance [Mul α] [IsLeftCancelMul α] : IsLeftCancelMul (Shrink.{v} α) :=
  (equivShrink α).symm.isLeftCancelMul

@[to_additive]
instance [Mul α] [IsRightCancelMul α] : IsRightCancelMul (Shrink.{v} α) :=
  (equivShrink α).symm.isRightCancelMul

@[to_additive]
instance [Mul α] [IsCancelMul α] : IsCancelMul (Shrink.{v} α) := (equivShrink α).symm.isCancelMul

@[to_additive]
noncomputable
instance [MulOneClass α] : MulOneClass (Shrink.{v} α) := (equivShrink α).symm.mulOneClass

@[to_additive]
noncomputable instance [Monoid α] : Monoid (Shrink.{v} α) := (equivShrink α).symm.monoid

@[to_additive]
noncomputable instance [CommMonoid α] : CommMonoid (Shrink.{v} α) := (equivShrink α).symm.commMonoid

@[to_additive]
noncomputable instance [Group α] : Group (Shrink.{v} α) := (equivShrink α).symm.group

@[to_additive]
noncomputable instance [CommGroup α] : CommGroup (Shrink.{v} α) := (equivShrink α).symm.commGroup

@[to_additive]
noncomputable
instance [Monoid M] [MulAction M α] : MulAction M (Shrink.{v} α) := (equivShrink α).symm.mulAction M

end Shrink
