/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Mathlib.Algebra.CovariantAndContravariant
import Mathlib.Algebra.Order.Monoid.Lemmas
import Mathlib.Data.Nat.Cast.Defs

/-!
# Typeclass expressing `0 ≤ 1`.
-/

open Function

/-- Typeclass for expressing that the `0` of a type is less or equal to its `1`. -/
class ZeroLEOneClass (α : Type _) [Zero α] [One α] [LE α] where
  zero_le_one : (0 : α) ≤ 1
#align zero_le_one_class ZeroLEOneClass

@[simp]
theorem zero_le_one [Zero α] [One α] [LE α] [ZeroLEOneClass α] : (0 : α) ≤ 1 :=
  ZeroLEOneClass.zero_le_one
#align zero_le_one zero_le_one

-- `zero_le_one` with an explicit type argument.
theorem zero_le_one' (α) [Zero α] [One α] [LE α] [ZeroLEOneClass α] : (0 : α) ≤ 1 :=
  zero_le_one
#align zero_le_one' zero_le_one'

theorem zero_le_two [Preorder α] [One α] [AddZeroClass α] [ZeroLEOneClass α]
  [CovariantClass α α (· + ·) (· ≤ ·)] :
    (0 : α) ≤ (2 : ℕ).unaryCast := by
  refine add_nonneg ?_ zero_le_one
  refine add_nonneg rfl.le zero_le_one
#align zero_le_two zero_le_two

theorem zero_le_three [Preorder α] [One α] [AddZeroClass α] [ZeroLEOneClass α]
  [CovariantClass α α (· + ·) (· ≤ ·)] :
    (0 : α) ≤ (3 : ℕ).unaryCast :=
  add_nonneg zero_le_two zero_le_one
#align zero_le_three zero_le_three

theorem zero_le_four [Preorder α] [One α] [AddZeroClass α] [ZeroLEOneClass α]
  [CovariantClass α α (· + ·) (· ≤ ·)] :
    (0 : α) ≤ (4 : ℕ).unaryCast :=
  add_nonneg zero_le_three zero_le_one
#align zero_le_four zero_le_four

lemma one_add_one [One α] [AddZeroClass α] : (1 : α) + 1 = (2 : ℕ).unaryCast := by
  change 1 + 1 = (0 + 1) + 1
  rw [zero_add 1]

theorem one_le_two [LE α] [One α] [AddZeroClass α] [ZeroLEOneClass α]
  [CovariantClass α α (· + ·) (· ≤ ·)] :
    (1 : α) ≤ (2 : ℕ).unaryCast := by
  rw [← add_zero 1, ← one_add_one]
  exact add_le_add_left zero_le_one _
#align one_le_two one_le_two

theorem one_le_two' [LE α] [One α] [AddZeroClass α] [ZeroLEOneClass α]
  [CovariantClass α α (swap (· + ·)) (· ≤ ·)] :
    (1 : α) ≤ (2 : ℕ).unaryCast := by
  rw [← zero_add 1, ← one_add_one]
  exact add_le_add_right zero_le_one _
#align one_le_two' one_le_two'
