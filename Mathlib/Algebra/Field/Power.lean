/-
Copyright (c) 2014 Robert Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Lewis, Leonardo de Moura, Johannes Hölzl, Mario Carneiro

! This file was ported from Lean 3 source module algebra.field.power
! leanprover-community/mathlib commit 1e05171a5e8cf18d98d9cf7b207540acb044acae
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.GroupWithZero.Power
import Mathlib.Algebra.Parity

/-!
# Results about powers in fields or division rings.

This file exists to ensure we can define `field` with minimal imports,
so contains some lemmas about powers of elements which need imports
beyond those needed for the basic definition.
-/


variable {α : Type _}

section DivisionRing

variable [DivisionRing α] {n : ℤ}

@[simp]
theorem zpow_bit1_neg (a : α) (n : ℤ) : (-a) ^ bit1 n = -a ^ bit1 n := by
  rw [zpow_bit1', zpow_bit1', neg_mul_neg, neg_mul_eq_mul_neg]
#align zpow_bit1_neg zpow_bit1_neg

theorem Odd.neg_zpow (h : Odd n) (a : α) : (-a) ^ n = -a ^ n :=
  by
  obtain ⟨k, rfl⟩ := h.exists_bit1
  exact zpow_bit1_neg _ _
#align odd.neg_zpow Odd.neg_zpow

theorem Odd.neg_one_zpow (h : Odd n) : (-1 : α) ^ n = -1 := by rw [h.neg_zpow, one_zpow]
#align odd.neg_one_zpow Odd.neg_one_zpow

end DivisionRing

