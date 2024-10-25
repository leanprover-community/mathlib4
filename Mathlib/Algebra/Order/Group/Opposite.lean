/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Group.Opposite

/-!
# Order instances for `MulOpposite`/`AddOpposite`

This files transfers order instances and ordered monoid/group instances from `α` to `αᵐᵒᵖ` and
`αᵃᵒᵖ`.
-/

variable {α : Type*}

namespace MulOpposite
section Preorder
variable [Preorder α]

@[to_additive] instance : Preorder αᵐᵒᵖ := Preorder.lift unop

@[to_additive (attr := simp)] lemma unop_le_unop {a b : αᵐᵒᵖ} : a.unop ≤ b.unop ↔ a ≤ b := .rfl
@[to_additive (attr := simp)] lemma op_le_op {a b : α} : op a ≤ op b ↔ a ≤ b := .rfl

end Preorder

@[to_additive] instance [PartialOrder α] : PartialOrder αᵐᵒᵖ := PartialOrder.lift _ unop_injective

section OrderedCommMonoid
variable [OrderedCommMonoid α]

@[to_additive] instance : OrderedCommMonoid αᵐᵒᵖ where
  mul_le_mul_left a b hab c := mul_le_mul_right' (by simpa) c.unop

@[to_additive (attr := simp)] lemma unop_le_one {a : αᵐᵒᵖ} : unop a ≤ 1 ↔ a ≤ 1 := .rfl
@[to_additive (attr := simp)] lemma one_le_unop {a : αᵐᵒᵖ} : 1 ≤ unop a ↔ 1 ≤ a := .rfl
@[to_additive (attr := simp)] lemma op_le_one {a : α} : op a ≤ 1 ↔ a ≤ 1 := .rfl
@[to_additive (attr := simp)] lemma one_le_op {a : α} : 1 ≤ op a ↔ 1 ≤ a := .rfl

end OrderedCommMonoid

@[to_additive] instance [OrderedCommGroup α] : OrderedCommGroup αᵐᵒᵖ where
  __ := instCommGroup
  __ := instOrderedCommMonoid

section OrderedAddCommMonoid
variable [OrderedAddCommMonoid α]

instance : OrderedAddCommMonoid αᵐᵒᵖ where
  add_le_add_left a b hab c := add_le_add_left (by simpa) c.unop

@[simp] lemma unop_nonneg {a : αᵐᵒᵖ} : unop a ≤ 0 ↔ a ≤ 0 := .rfl
@[simp] lemma unop_nonpos {a : αᵐᵒᵖ} : 0 ≤ unop a ↔ 0 ≤ a := .rfl
@[simp] lemma op_nonneg {a : α} : op a ≤ 0 ↔ a ≤ 0 := .rfl
@[simp] lemma op_nonpos {a : α} : 0 ≤ op a ↔ 0 ≤ a := .rfl

end OrderedAddCommMonoid

instance [OrderedAddCommGroup α] : OrderedAddCommGroup αᵐᵒᵖ where
  __ := instAddCommGroup
  __ := instOrderedAddCommMonoid

end MulOpposite

namespace AddOpposite
section OrderedCommMonoid
variable [OrderedCommMonoid α]

instance : OrderedCommMonoid αᵃᵒᵖ where
  mul_le_mul_left a b hab c := mul_le_mul_left' (by simpa) c.unop

@[simp] lemma unop_le_one {a : αᵃᵒᵖ} : unop a ≤ 1 ↔ a ≤ 1 := .rfl
@[simp] lemma one_le_unop {a : αᵃᵒᵖ} : 1 ≤ unop a ↔ 1 ≤ a := .rfl
@[simp] lemma op_le_one {a : α} : op a ≤ 1 ↔ a ≤ 1 := .rfl
@[simp] lemma one_le_op {a : α} : 1 ≤ op a ↔ 1 ≤ a := .rfl

end OrderedCommMonoid

instance [OrderedCommGroup α] : OrderedCommGroup αᵃᵒᵖ where
  __ := instCommGroup
  __ := instOrderedCommMonoid

end AddOpposite
