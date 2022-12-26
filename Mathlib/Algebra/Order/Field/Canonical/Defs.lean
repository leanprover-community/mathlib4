/-
Copyright (c) 2014 Robert Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Lewis, Leonardo de Moura, Mario Carneiro, Floris van Doorn
Ported by: Rémy Degenne

! This file was ported from Lean 3 source module algebra.order.field.canonical.defs
! leanprover-community/mathlib commit fc2ed6f838ce7c9b7c7171e58d78eaf7b438fb0e
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.Order.Field.Defs
import Mathlib.Algebra.Order.Ring.Canonical
import Mathlib.Algebra.Order.WithZero

/-!
# Canonically ordered semifields
-/


variable {α : Type _}

/-- A canonically linear ordered field is a linear ordered field in which `a ≤ b` iff there exists
`c` with `b = a + c`. -/
class CanonicallyLinearOrderedSemifield (α : Type _) extends CanonicallyOrderedCommSemiring α,
  LinearOrderedSemifield α
#align canonically_linear_ordered_semifield CanonicallyLinearOrderedSemifield

-- See note [lower instance priority]
instance (priority := 100) CanonicallyLinearOrderedSemifield.toLinearOrderedCommGroupWithZero
    [CanonicallyLinearOrderedSemifield α] : LinearOrderedCommGroupWithZero α :=
  { ‹CanonicallyLinearOrderedSemifield α› with
    mul_le_mul_left := fun a b h c ↦ mul_le_mul_of_nonneg_left h <| zero_le _ }
#align
  canonically_linear_ordered_semifield.to_linear_ordered_comm_group_with_zero
  CanonicallyLinearOrderedSemifield.toLinearOrderedCommGroupWithZero

-- See note [lower instance priority]
instance (priority := 100) CanonicallyLinearOrderedSemifield.toCanonicallyLinearOrderedAddMonoid
    [CanonicallyLinearOrderedSemifield α] : CanonicallyLinearOrderedAddMonoid α :=
  { ‹CanonicallyLinearOrderedSemifield α› with }
#align
  canonically_linear_ordered_semifield.to_canonically_linear_ordered_add_monoid
  CanonicallyLinearOrderedSemifield.toCanonicallyLinearOrderedAddMonoid
