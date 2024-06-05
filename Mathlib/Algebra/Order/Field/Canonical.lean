/-
Copyright (c) 2014 Robert Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Lewis, Leonardo de Moura, Mario Carneiro, Floris van Doorn
-/
import Mathlib.Algebra.Order.Field.Defs
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Algebra.Order.Ring.Canonical

#align_import algebra.order.field.canonical.defs from "leanprover-community/mathlib"@"fc2ed6f838ce7c9b7c7171e58d78eaf7b438fb0e"
#align_import algebra.order.field.canonical.basic from "leanprover-community/mathlib"@"ee0c179cd3c8a45aa5bffbf1b41d8dbede452865"

/-!
# Canonically ordered semifields
-/


variable {α : Type*} [LinearOrderedSemifield α] [CanonicallyOrderedAdd α]

@[nolint docBlame]
abbrev CanonicallyOrderedAdd.toLinearOrderedCommGroupWithZero :
    LinearOrderedCommGroupWithZero α :=
  { ‹LinearOrderedSemifield α› with
    mul_le_mul_left := fun a b h c ↦ mul_le_mul_of_nonneg_left h <| zero_le _ }
#align canonically_linear_ordered_semifield.to_linear_ordered_comm_group_with_zero CanonicallyOrderedAdd.toLinearOrderedCommGroupWithZero

variable [Sub α] [OrderedSub α]

theorem tsub_div (a b c : α) : (a - b) / c = a / c - b / c := by simp_rw [div_eq_mul_inv, tsub_mul]
#align tsub_div tsub_div
