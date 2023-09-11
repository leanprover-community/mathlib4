/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Order.Basic

#align_import data.nat.cast.basic from "leanprover-community/mathlib"@"acebd8d49928f6ed8920e502a6c90674e75bd441"

/-!
# Cast of natural numbers

A variant of `Nat.cast_sub` that works for `ℝ≥0` and `ℚ≥0`.

This is exiled from `Mathlib.Data.Nat.Cast.Basic` as it requires a relatively expensive import,
and that file is on the path to significant tactics.
-/

variable {α : Type*}

namespace Nat

/-- A version of `Nat.cast_sub` that works for `ℝ≥0` and `ℚ≥0`. Note that this proof doesn't work
for `ℕ∞` and `ℝ≥0∞`, so we use type-specific lemmas for these types. -/
@[simp, norm_cast]
theorem cast_tsub [CanonicallyOrderedCommSemiring α] [Sub α] [OrderedSub α]
    [ContravariantClass α α (· + ·) (· ≤ ·)] (m n : ℕ) : ↑(m - n) = (m - n : α) := by
  cases' le_total m n with h h
  · rw [Nat.sub_eq_zero_of_le h, cast_zero, tsub_eq_zero_of_le]
    exact mono_cast h
  · rcases le_iff_exists_add'.mp h with ⟨m, rfl⟩
    rw [add_tsub_cancel_right, cast_add, add_tsub_cancel_right]
#align nat.cast_tsub Nat.cast_tsub
