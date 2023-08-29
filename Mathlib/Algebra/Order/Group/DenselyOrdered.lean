/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Monoid.OrderDual

#align_import algebra.order.group.densely_ordered from "leanprover-community/mathlib"@"4e87c8477c6c38b753f050bc9664b94ee859896c"

/-!
# Lemmas about densely linearly ordered groups.
-/


variable {α : Type*}

section DenselyOrdered

variable [Group α] [LinearOrder α]

variable [CovariantClass α α (· * ·) (· ≤ ·)]

variable [DenselyOrdered α] {a b c : α}

@[to_additive]
theorem le_of_forall_lt_one_mul_le (h : ∀ ε < 1, a * ε ≤ b) : a ≤ b :=
  @le_of_forall_one_lt_le_mul αᵒᵈ _ _ _ _ _ _ _ _ h
#align le_of_forall_lt_one_mul_le le_of_forall_lt_one_mul_le
#align le_of_forall_neg_add_le le_of_forall_neg_add_le

@[to_additive]
theorem le_of_forall_one_lt_div_le (h : ∀ ε : α, 1 < ε → a / ε ≤ b) : a ≤ b :=
  le_of_forall_lt_one_mul_le fun ε ε1 => by
    simpa only [div_eq_mul_inv, inv_inv] using h ε⁻¹ (Left.one_lt_inv_iff.2 ε1)
    -- 🎉 no goals
#align le_of_forall_one_lt_div_le le_of_forall_one_lt_div_le
#align le_of_forall_pos_sub_le le_of_forall_pos_sub_le

@[to_additive]
theorem le_iff_forall_one_lt_le_mul : a ≤ b ↔ ∀ ε, 1 < ε → a ≤ b * ε :=
  ⟨fun h _ ε_pos => le_mul_of_le_of_one_le h ε_pos.le, le_of_forall_one_lt_le_mul⟩
#align le_iff_forall_one_lt_le_mul le_iff_forall_one_lt_le_mul
#align le_iff_forall_pos_le_add le_iff_forall_pos_le_add

@[to_additive]
theorem le_iff_forall_lt_one_mul_le : a ≤ b ↔ ∀ ε < 1, a * ε ≤ b :=
  @le_iff_forall_one_lt_le_mul αᵒᵈ _ _ _ _ _ _
#align le_iff_forall_lt_one_mul_le le_iff_forall_lt_one_mul_le
#align le_iff_forall_neg_add_le le_iff_forall_neg_add_le

end DenselyOrdered
