/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Opposite
public import Mathlib.Algebra.Order.Monoid.Defs

set_option doc.verso true
set_option doc.verso.suggestions false

/-!
# Order instances for `MulOpposite`/`AddOpposite`

This file transfers order instances and ordered monoid/group instances from `α` to `αᵐᵒᵖ` and
`αᵃᵒᵖ`.
-/

public section

variable {α : Type*}

namespace MulOpposite
section Preorder
variable [Preorder α]

@[to_additive] instance : Preorder αᵐᵒᵖ := Preorder.lift unop

@[to_additive (attr := simp)] lemma unop_le_unop {a b : αᵐᵒᵖ} : a.unop ≤ b.unop ↔ a ≤ b := .rfl
@[to_additive (attr := simp)] lemma op_le_op {a b : α} : op a ≤ op b ↔ a ≤ b := .rfl
@[to_additive (attr := simp)] lemma unop_lt_unop {a b : αᵐᵒᵖ} : a.unop < b.unop ↔ a < b := .rfl
@[to_additive (attr := simp)] lemma op_lt_op {a b : α} : op a < op b ↔ a < b := .rfl

end Preorder

@[to_additive] instance [PartialOrder α] : PartialOrder αᵐᵒᵖ := PartialOrder.lift _ unop_injective

@[to_additive] instance [Max α] : Max αᵐᵒᵖ where max a b := op (a.unop ⊔ b.unop)
@[to_additive] instance [Min α] : Min αᵐᵒᵖ where min a b := op (a.unop ⊓ b.unop)
@[to_additive] instance [Ord α] : Ord αᵐᵒᵖ where compare a b := compare a.unop b.unop

@[to_additive (attr := simp)] lemma op_sup [Max α] (a b : α) : op (a ⊔ b) = op a ⊔ op b := rfl
@[to_additive (attr := simp)]
lemma unop_sup [Max α] (a b : αᵐᵒᵖ) : unop (a ⊔ b) = unop a ⊔ unop b := rfl
@[to_additive (attr := simp)] lemma op_inf [Min α] (a b : α) : op (a ⊓ b) = op a ⊓ op b := rfl
@[to_additive (attr := simp)]
lemma unop_inf [Min α] (a b : αᵐᵒᵖ) : unop (a ⊓ b) = unop a ⊓ unop b := rfl
@[to_additive (attr := simp)]
lemma op_compare [Ord α] (a b : α) : compare (op a) (op b) = compare a b := rfl
@[to_additive (attr := simp)]
lemma unop_compare [Ord α] (a b : αᵐᵒᵖ) : compare (unop a) (unop b) = compare a b := rfl

@[to_additive] instance [LinearOrder α] : LinearOrder αᵐᵒᵖ :=
  letI : DecidableLE αᵐᵒᵖ := fun a b ↦ inferInstanceAs (Decidable (a.unop ≤ b.unop))
  letI : DecidableLT αᵐᵒᵖ := fun a b ↦ inferInstanceAs (Decidable (a.unop < b.unop))
  unop_injective.linearOrder _ .rfl .rfl (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

section OrderedCommMonoid
variable [CommMonoid α] [Preorder α]

@[to_additive] instance [IsOrderedMonoid α] : IsOrderedMonoid αᵐᵒᵖ where
  mul_le_mul_left a b hab c := mul_le_mul_right (by simpa) c.unop

@[to_additive] instance [IsOrderedCancelMonoid α] : IsOrderedCancelMonoid αᵐᵒᵖ where
  le_of_mul_le_mul_left _a _b _c h := le_of_mul_le_mul_right' (α := α) h

@[to_additive (attr := simp)] lemma unop_le_one {a : αᵐᵒᵖ} : unop a ≤ 1 ↔ a ≤ 1 := .rfl
@[to_additive (attr := simp)] lemma one_le_unop {a : αᵐᵒᵖ} : 1 ≤ unop a ↔ 1 ≤ a := .rfl
@[to_additive (attr := simp)] lemma op_le_one {a : α} : op a ≤ 1 ↔ a ≤ 1 := .rfl
@[to_additive (attr := simp)] lemma one_le_op {a : α} : 1 ≤ op a ↔ 1 ≤ a := .rfl
@[to_additive (attr := simp) unop_lt_zero]
lemma unop_lt_one {a : αᵐᵒᵖ} : unop a < 1 ↔ a < 1 := .rfl
@[to_additive (attr := simp) unop_pos] lemma one_lt_unop {a : αᵐᵒᵖ} : 1 < unop a ↔ 1 < a := .rfl
@[to_additive (attr := simp) op_lt_zero] lemma op_lt_one {a : α} : op a < 1 ↔ a < 1 := .rfl
@[to_additive (attr := simp) op_pos] lemma one_lt_op {a : α} : 1 < op a ↔ 1 < a := .rfl

end OrderedCommMonoid

section OrderedAddCommMonoid
variable [AddCommMonoid α] [Preorder α]

instance [IsOrderedAddMonoid α] : IsOrderedAddMonoid αᵐᵒᵖ where
  add_le_add_left a b hab c := add_le_add_left (by simpa) c.unop

instance [IsOrderedCancelAddMonoid α] : IsOrderedCancelAddMonoid αᵐᵒᵖ where
  le_of_add_le_add_left _a _b _c h := le_of_add_le_add_left (α := α) h

@[simp] lemma unop_nonpos {a : αᵐᵒᵖ} : unop a ≤ 0 ↔ a ≤ 0 := .rfl
@[simp] lemma unop_nonneg {a : αᵐᵒᵖ} : 0 ≤ unop a ↔ 0 ≤ a := .rfl
@[simp] lemma op_nonpos {a : α} : op a ≤ 0 ↔ a ≤ 0 := .rfl
@[simp] lemma op_nonneg {a : α} : 0 ≤ op a ↔ 0 ≤ a := .rfl
@[simp] lemma unop_lt_zero {a : αᵐᵒᵖ} : unop a < 0 ↔ a < 0 := .rfl
@[simp] lemma unop_pos {a : αᵐᵒᵖ} : 0 < unop a ↔ 0 < a := .rfl
@[simp] lemma op_lt_zero {a : α} : op a < 0 ↔ a < 0 := .rfl
@[simp] lemma op_pos {a : α} : 0 < op a ↔ 0 < a := .rfl

end OrderedAddCommMonoid

end MulOpposite

namespace AddOpposite
section OrderedCommMonoid
variable [CommMonoid α] [Preorder α]

instance [IsOrderedMonoid α] : IsOrderedMonoid αᵃᵒᵖ where
  mul_le_mul_left a b hab c := mul_le_mul_left (by simpa) c.unop

instance [IsOrderedCancelMonoid α] : IsOrderedCancelMonoid αᵃᵒᵖ where
  le_of_mul_le_mul_left _a _b _c h := le_of_mul_le_mul_left' (α := α) h

@[simp] lemma unop_le_one {a : αᵃᵒᵖ} : unop a ≤ 1 ↔ a ≤ 1 := .rfl
@[simp] lemma one_le_unop {a : αᵃᵒᵖ} : 1 ≤ unop a ↔ 1 ≤ a := .rfl
@[simp] lemma op_le_one {a : α} : op a ≤ 1 ↔ a ≤ 1 := .rfl
@[simp] lemma one_le_op {a : α} : 1 ≤ op a ↔ 1 ≤ a := .rfl
@[simp] lemma unop_lt_one {a : αᵃᵒᵖ} : unop a < 1 ↔ a < 1 := .rfl
@[simp] lemma one_lt_unop {a : αᵃᵒᵖ} : 1 < unop a ↔ 1 < a := .rfl
@[simp] lemma op_lt_one {a : α} : op a < 1 ↔ a < 1 := .rfl
@[simp] lemma one_lt_op {a : α} : 1 < op a ↔ 1 < a := .rfl

end OrderedCommMonoid

end AddOpposite
