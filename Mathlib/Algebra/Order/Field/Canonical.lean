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

set_option linter.deprecated false in
/-- A canonically linear ordered field is a linear ordered field in which `a ≤ b` iff there exists
`c` with `b = a + c`. -/
@[deprecated "Use `[LinearOrderedSemifield α] [CanonicallyOrderedAdd α]` instead."
  (since := "2025-01-13")]
structure CanonicallyLinearOrderedSemifield (α : Type*) extends CanonicallyOrderedCommSemiring α,
  LinearOrderedSemifield α

attribute [nolint docBlame] CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield

variable {α : Type*} [LinearOrderedSemifield α] [CanonicallyOrderedAdd α]

-- See note [reducible non-instances]
/-- Construct a `LinearOrderedCommGroupWithZero` from a canonically ordered
`LinearOrderedSemifield`. -/
abbrev LinearOrderedSemifield.toLinearOrderedCommGroupWithZero :
    LinearOrderedCommGroupWithZero α where
  __ := ‹LinearOrderedSemifield α›
  bot := 0
  bot_le := zero_le
  mul_le_mul_left _ _ h _:= mul_le_mul_of_nonneg_left h <| zero_le _

variable [Sub α] [OrderedSub α]

theorem tsub_div (a b c : α) : (a - b) / c = a / c - b / c := by simp_rw [div_eq_mul_inv, tsub_mul]
