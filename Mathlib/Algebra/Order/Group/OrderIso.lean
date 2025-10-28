/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Order.Hom.Basic

/-!
# Inverse and multiplication as order isomorphisms in ordered groups

-/

open Function

universe u

variable {α : Type u}

section Group

variable [Group α]

section TypeclassesLeftRightLE

variable [LE α] [MulLeftMono α] [MulRightMono α] {a b : α}

section

variable (α)

/-- `x ↦ x⁻¹` as an order-reversing equivalence. -/
@[to_additive (attr := simps!) /-- `x ↦ -x` as an order-reversing equivalence. -/]
def OrderIso.inv : α ≃o αᵒᵈ where
  toEquiv := (Equiv.inv α).trans OrderDual.toDual
  map_rel_iff' {_ _} := inv_le_inv_iff (α := α)

end

@[to_additive neg_le]
theorem inv_le' : a⁻¹ ≤ b ↔ b⁻¹ ≤ a :=
  (OrderIso.inv α).symm_apply_le

alias ⟨inv_le_of_inv_le', _⟩ := inv_le'

attribute [to_additive neg_le_of_neg_le] inv_le_of_inv_le'

@[to_additive le_neg]
theorem le_inv' : a ≤ b⁻¹ ↔ b ≤ a⁻¹ :=
  (OrderIso.inv α).le_symm_apply

/-- `x ↦ a / x` as an order-reversing equivalence. -/
@[to_additive (attr := simps!) /-- `x ↦ a - x` as an order-reversing equivalence. -/]
def OrderIso.divLeft (a : α) : α ≃o αᵒᵈ where
  toEquiv := (Equiv.divLeft a).trans OrderDual.toDual
  map_rel_iff' {_ _} := div_le_div_iff_left (α := α) _

end TypeclassesLeftRightLE

end Group

alias ⟨le_inv_of_le_inv, _⟩ := le_inv'

attribute [to_additive] le_inv_of_le_inv

section Group

variable [Group α] [LE α]

section Right

variable [MulRightMono α] {a : α}

/-- `Equiv.mulRight` as an `OrderIso`. See also `OrderEmbedding.mulRight`. -/
@[to_additive (attr := simps! +simpRhs toEquiv apply)
  /-- `Equiv.addRight` as an `OrderIso`. See also `OrderEmbedding.addRight`. -/]
def OrderIso.mulRight (a : α) : α ≃o α where
  map_rel_iff' {_ _} := mul_le_mul_iff_right a
  toEquiv := Equiv.mulRight a

@[to_additive (attr := simp)]
theorem OrderIso.mulRight_symm (a : α) : (OrderIso.mulRight a).symm = OrderIso.mulRight a⁻¹ := by
  ext x
  rfl

/-- `x ↦ x / a` as an order isomorphism. -/
@[to_additive (attr := simps!) /-- `x ↦ x - a` as an order isomorphism. -/]
def OrderIso.divRight (a : α) : α ≃o α where
  toEquiv := Equiv.divRight a
  map_rel_iff' {_ _} := div_le_div_iff_right a

end Right

section Left

variable [MulLeftMono α]

/-- `Equiv.mulLeft` as an `OrderIso`. See also `OrderEmbedding.mulLeft`. -/
@[to_additive (attr := simps! +simpRhs toEquiv apply)
  /-- `Equiv.addLeft` as an `OrderIso`. See also `OrderEmbedding.addLeft`. -/]
def OrderIso.mulLeft (a : α) : α ≃o α where
  map_rel_iff' {_ _} := mul_le_mul_iff_left a
  toEquiv := Equiv.mulLeft a

@[to_additive (attr := simp)]
theorem OrderIso.mulLeft_symm (a : α) : (OrderIso.mulLeft a).symm = OrderIso.mulLeft a⁻¹ := by
  ext x
  rfl

end Left

end Group
