/-
Copyright (c) 2025 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/

import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Basic

@[simp]
theorem Int.isSquare_sign_iff {z : ℤ} : IsSquare z.sign ↔ 0 ≤ z := by
  induction z using Int.induction_on with
  | zero => simp
  | succ => norm_cast; simp
  | pred =>
    rw [sign_eq_neg_one_of_neg (by omega), ← neg_add', neg_nonneg]
    simp [not_isSquare_of_neg]
