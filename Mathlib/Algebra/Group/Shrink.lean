/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.Logic.Small.Defs
import Mathlib.Tactic.SuppressCompilation

/-!
# Transfer group structures from `α` to `Shrink α`
-/

-- FIXME: `to_additive` is incompatible with `noncomputable section`.
-- See https://github.com/leanprover-community/mathlib4/issues/1074.
suppress_compilation

universe v
variable {M α : Type*} [Small.{v} α]

namespace Shrink

@[to_additive] instance [One α] : One (Shrink.{v} α) := (equivShrink α).symm.one
@[to_additive] instance [Mul α] : Mul (Shrink.{v} α) := (equivShrink α).symm.mul
@[to_additive] instance [Div α] : Div (Shrink.{v} α) := (equivShrink α).symm.div
@[to_additive] instance [Inv α] : Inv (Shrink.{v} α) := (equivShrink α).symm.Inv
@[to_additive] instance [Pow α M] : Pow (Shrink.{v} α) M := (equivShrink α).symm.pow M

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
def mulEquiv [Mul α] : Shrink.{v} α ≃* α := (equivShrink α).symm.mulEquiv

@[to_additive]
instance [Semigroup α] : Semigroup (Shrink.{v} α) := (equivShrink α).symm.semigroup

@[to_additive]
instance [CommSemigroup α] : CommSemigroup (Shrink.{v} α) := (equivShrink α).symm.commSemigroup

@[to_additive]
instance [MulOneClass α] : MulOneClass (Shrink.{v} α) := (equivShrink α).symm.mulOneClass

@[to_additive]
instance [Monoid α] : Monoid (Shrink.{v} α) := (equivShrink α).symm.monoid

@[to_additive]
instance [CommMonoid α] : CommMonoid (Shrink.{v} α) := (equivShrink α).symm.commMonoid

@[to_additive]
instance [Group α] : Group (Shrink.{v} α) := (equivShrink α).symm.group

@[to_additive]
instance [CommGroup α] : CommGroup (Shrink.{v} α) := (equivShrink α).symm.commGroup

@[to_additive]
instance [Monoid M] [MulAction M α] : MulAction M (Shrink.{v} α) := (equivShrink α).symm.mulAction M

end Shrink
