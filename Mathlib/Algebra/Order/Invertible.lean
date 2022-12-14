/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Invertible

/-!
# Lemmas about `inv_of` in ordered (semi)rings.
-/

variable [LinearOrderedSemiring α] {a : α}

@[simp]
theorem invOf_pos [Invertible a] : 0 < ⅟ a ↔ 0 < a :=
  haveI : 0 < a * ⅟ a := by simp only [mul_invOf_self, zero_lt_one]
  ⟨fun h => pos_of_mul_pos_left this h.le, fun h => pos_of_mul_pos_right this h.le⟩
#align inv_of_pos invOf_pos

@[simp]
theorem invOf_nonpos [Invertible a] : ⅟ a ≤ 0 ↔ a ≤ 0 := by simp only [← not_lt, invOf_pos]; rfl
#align inv_of_nonpos invOf_nonpos

@[simp]
theorem invOf_nonneg [Invertible a] : 0 ≤ ⅟ a ↔ 0 ≤ a :=
  haveI : 0 < a * ⅟ a := by simp only [mul_invOf_self, zero_lt_one]
  ⟨fun h => (pos_of_mul_pos_left this h).le, fun h => (pos_of_mul_pos_right this h).le⟩
#align inv_of_nonneg invOf_nonneg

@[simp]
theorem invOf_lt_zero [Invertible a] : ⅟ a < 0 ↔ a < 0 := by simp only [← not_le, invOf_nonneg]; rfl
#align inv_of_lt_zero invOf_lt_zero

@[simp]
theorem invOf_le_one [Invertible a] (h : 1 ≤ a) : ⅟ a ≤ 1 :=
  mul_invOf_self a ▸ le_mul_of_one_le_left (invOf_nonneg.2 <| zero_le_one.trans h) h
#align inv_of_le_one invOf_le_one
