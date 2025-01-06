/-
Copyright (c) 2014 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Leonardo de Moura, Mario Carneiro, Floris van Doorn
-/
import Mathlib.Algebra.Order.Field.Defs
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Algebra.Order.Ring.Canonical

/-!
# Canonically ordered semifields
-/


variable {α : Type*} [LinearOrderedSemifield α] [CanonicallyOrderedAdd α]

-- See note [reducible non-instances]
/-- Construct a `LinearOrderedCommGroupWithZero` from a canonically ordered
`LinearOrderedSemifield`. -/
abbrev LinearOrderedSemifield.toLinearOrderedCommGroupWithZero :
    LinearOrderedCommGroupWithZero α :=
  { ‹LinearOrderedSemifield α› with
    mul_le_mul_left := fun _ _ h _ ↦ mul_le_mul_of_nonneg_left h <| zero_le _ }

variable [Sub α] [OrderedSub α]

theorem tsub_div (a b c : α) : (a - b) / c = a / c - b / c := by simp_rw [div_eq_mul_inv, tsub_mul]
