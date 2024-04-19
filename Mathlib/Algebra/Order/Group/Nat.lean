/-
Copyright (c) 2014 Floris van Doorn (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
import Mathlib.Algebra.Group.Nat
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.Sub.Defs
import Mathlib.Data.Nat.Defs

#align_import data.nat.order.basic from "leanprover-community/mathlib"@"3ed3f98a1e836241990d3d308f1577e434977130"

/-!
# The naturals form a linear ordered monoid

This file contains the linear ordered monoid instance on the natural numbers.

See note [foundational algebra order theory].
-/

namespace Nat

/-! ### Instances -/

instance canonicallyLinearOrderedAddCommMonoid : CanonicallyLinearOrderedAddCommMonoid ℕ where
  __ := linearOrder
  bot := 0
  bot_le := Nat.zero_le
  add_le_add_left := @Nat.add_le_add_left
  le_self_add := Nat.le_add_right
  exists_add_of_le := Nat.exists_eq_add_of_le

instance linearOrderedCommMonoid : LinearOrderedCommMonoid ℕ where
  __ := linearOrder
  __ := commMonoid
  mul_le_mul_left _ _ h _ := mul_le_mul_left _ h

instance linearOrderedCancelAddCommMonoid : LinearOrderedCancelAddCommMonoid ℕ where
  __ := linearOrder
  add_le_add_left := @Nat.add_le_add_left
  le_of_add_le_add_left := @Nat.le_of_add_le_add_left

instance instOrderedSub : OrderedSub ℕ := by
  refine ⟨fun m n k ↦ ?_⟩
  induction' n with n ih generalizing k
  · simp
  · simp only [sub_succ, pred_le_iff, ih, succ_add, add_succ]

/-!
### Extra instances to short-circuit type class resolution

These also prevent non-computable instances being used to construct these instances non-computably.
-/

instance orderBot : OrderBot ℕ := by infer_instance
#align nat.order_bot Nat.orderBot

/-! ### Miscellaneous lemmas -/

theorem _root_.NeZero.one_le {n : ℕ} [NeZero n] : 1 ≤ n := one_le_iff_ne_zero.mpr (NeZero.ne n)

end Nat
