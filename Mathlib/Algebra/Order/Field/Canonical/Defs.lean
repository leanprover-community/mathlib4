/-
Copyright (c) 2014 Robert Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Lewis, Leonardo de Moura, Mario Carneiro, Floris van Doorn
-/
import Mathlib.Algebra.Order.Field.Defs
import Mathlib.Algebra.Order.Ring.Canonical
import Mathlib.Algebra.Order.WithZero

#align_import algebra.order.field.canonical.defs from "leanprover-community/mathlib"@"fc2ed6f838ce7c9b7c7171e58d78eaf7b438fb0e"

/-!
# Canonically ordered semifields
-/


variable {α : Type _} [LinearOrderedSemifield α] [CanonicallyOrderedAdd α]

-- See note [lower instance priority]
instance (priority := 100) CanonicallyOrderedAdd.toLinearOrderedCommGroupWithZero :
    LinearOrderedCommGroupWithZero α :=
  { ‹LinearOrderedSemifield α› with
    mul_le_mul_left := fun a b h c ↦ mul_le_mul_of_nonneg_left h <| zero_le _ }
#align canonically_linear_ordered_semifield.to_linear_ordered_comm_group_with_zero CanonicallyOrderedAdd.toLinearOrderedCommGroupWithZero
