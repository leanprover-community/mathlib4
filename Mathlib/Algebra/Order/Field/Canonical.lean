/-
Copyright (c) 2014 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Leonardo de Moura, Mario Carneiro, Floris van Doorn
-/
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Algebra.Order.Ring.Canonical

/-!
# Canonically ordered semifields
-/

variable {α : Type*} [Semifield α] [LinearOrder α] [CanonicallyOrderedAdd α]

-- See note [reducible non-instances]
/-- Construct a `LinearOrderedCommGroupWithZero` from a canonically linear ordered semifield. -/
abbrev CanonicallyOrderedAdd.toLinearOrderedCommGroupWithZero :
    LinearOrderedCommGroupWithZero α where
  __ := ‹Semifield α›
  __ := ‹LinearOrder α›
  bot := 0
  bot_le := zero_le
  zero_le_one := zero_le_one
  mul_le_mul_left := fun _ _ h _ ↦ mul_le_mul_of_nonneg_left h <| zero_le _

variable [IsStrictOrderedRing α] [Sub α] [OrderedSub α]

theorem tsub_div (a b c : α) : (a - b) / c = a / c - b / c := by simp_rw [div_eq_mul_inv, tsub_mul]
