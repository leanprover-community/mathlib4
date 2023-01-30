/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
Ported by: Scott Morrison

! This file was ported from Lean 3 source module algebra.order.group.order_iso
! leanprover-community/mathlib commit a95b16cbade0f938fc24abd05412bde1e84bab9b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Hom.Equiv.Units.Basic

/-!
# Inverse and multiplication as order isomorphisms in ordered groups

-/

open Function

universe u

variable {α : Type u}

section Group

variable [Group α]

section TypeclassesLeftRightLE

variable [LE α] [CovariantClass α α (· * ·) (· ≤ ·)] [CovariantClass α α (swap (· * ·)) (· ≤ ·)]
  {a b c d : α}

section

variable (α)

/-- `x ↦ x⁻¹` as an order-reversing equivalence. -/
@[to_additive "`x ↦ -x` as an order-reversing equivalence.", simps]
def OrderIso.inv : α ≃o αᵒᵈ where
  toEquiv := (Equiv.inv α).trans OrderDual.toDual
  map_rel_iff' {_ _} := @inv_le_inv_iff α _ _ _ _ _ _
#align order_iso.inv OrderIso.inv
#align order_iso.neg OrderIso.neg
#align order_iso.inv_apply OrderIso.inv_apply
#align order_iso.inv_symm_apply OrderIso.inv_symmApply

end

@[to_additive neg_le]
theorem inv_le' : a⁻¹ ≤ b ↔ b⁻¹ ≤ a :=
  (OrderIso.inv α).symm_apply_le
#align inv_le' inv_le'
#align neg_le neg_le

alias inv_le' ↔ inv_le_of_inv_le' _
#align inv_le_of_inv_le' inv_le_of_inv_le'

attribute [to_additive neg_le_of_neg_le] inv_le_of_inv_le'
#align neg_le_of_neg_le neg_le_of_neg_le

@[to_additive le_neg]
theorem le_inv' : a ≤ b⁻¹ ↔ b ≤ a⁻¹ :=
  (OrderIso.inv α).le_symm_apply
#align le_inv' le_inv'
#align le_neg le_neg

end TypeclassesLeftRightLE

end Group

alias le_inv' ↔ le_inv_of_le_inv _
#align le_inv_of_le_inv le_inv_of_le_inv

attribute [to_additive] le_inv_of_le_inv
#align le_neg_of_le_neg le_neg_of_le_neg

section Group

variable [Group α] [LE α]

section Right

variable [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c d : α}

/-- `Equiv.mulRight` as an `OrderIso`. See also `OrderEmbedding.mulRight`. -/
@[to_additive "`Equiv.addRight` as an `OrderIso`. See also `OrderEmbedding.addRight`.",
  simps (config := { simpRhs := true }) toEquiv apply]
def OrderIso.mulRight (a : α) : α ≃o α where
  map_rel_iff' {_ _} := mul_le_mul_iff_right a
  toEquiv := Equiv.mulRight a
#align order_iso.mul_right OrderIso.mulRight
#align order_iso.add_right OrderIso.addRight
#align order_iso.mul_right_apply OrderIso.mulRight_apply
#align order_iso.mul_right_to_equiv OrderIso.mulRight_toEquiv

@[to_additive (attr := simp)]
theorem OrderIso.mulRight_symm (a : α) : (OrderIso.mulRight a).symm = OrderIso.mulRight a⁻¹ := by
  ext x
  rfl
#align order_iso.mul_right_symm OrderIso.mulRight_symm
#align order_iso.add_right_symm OrderIso.addRight_symm

end Right

section Left

variable [CovariantClass α α (· * ·) (· ≤ ·)]

/-- `Equiv.mulLeft` as an `OrderIso`. See also `OrderEmbedding.mulLeft`. -/
@[to_additive "`Equiv.addLeft` as an `OrderIso`. See also `OrderEmbedding.addLeft`.",
  simps (config := { simpRhs := true }) toEquiv apply]
def OrderIso.mulLeft (a : α) : α ≃o α where
  map_rel_iff' {_ _} := mul_le_mul_iff_left a
  toEquiv := Equiv.mulLeft a
#align order_iso.mul_left OrderIso.mulLeft
#align order_iso.add_left OrderIso.addLeft
#align order_iso.mul_left_apply OrderIso.mulLeft_apply
#align order_iso.mul_left_to_equiv OrderIso.mulLeft_toEquiv

@[to_additive (attr := simp)]
theorem OrderIso.mulLeft_symm (a : α) : (OrderIso.mulLeft a).symm = OrderIso.mulLeft a⁻¹ := by
  ext x
  rfl
#align order_iso.mul_left_symm OrderIso.mulLeft_symm
#align order_iso.add_left_symm OrderIso.addLeft_symm

end Left

end Group
