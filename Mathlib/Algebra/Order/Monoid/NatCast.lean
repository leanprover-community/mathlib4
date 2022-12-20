/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl, Yuyang Zhao

! This file was ported from Lean 3 source module algebra.order.monoid.nat_cast
! leanprover-community/mathlib commit 07fee0ca54c320250c98bacf31ca5f288b2bcbe2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.Order.Monoid.Lemmas
import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.Data.Nat.Cast.Defs

/-!
# Order of numerals in an `AddMonoidWithOne`.
-/

variable {α : Type _}

open Function

lemma lt_add_one [One α] [AddZeroClass α] [PartialOrder α] [ZeroLEOneClass α]
  [NeZero (1 : α)] [CovariantClass α α (·+·) (·<·)] (a : α) : a < a + 1 :=
lt_add_of_pos_right _ zero_lt_one

lemma lt_one_add [One α] [AddZeroClass α] [PartialOrder α] [ZeroLEOneClass α]
  [NeZero (1 : α)] [CovariantClass α α (swap (·+·)) (·<·)] (a : α) : a < 1 + a :=
lt_add_of_pos_left _ zero_lt_one

variable [AddMonoidWithOne α]

lemma zero_le_two [Preorder α] [ZeroLEOneClass α] [CovariantClass α α (·+·) (·≤·)] :
    (0 : α) ≤ 2 := by
  rw [← one_add_one_eq_two]
  exact add_nonneg zero_le_one zero_le_one

lemma zero_le_three [Preorder α] [ZeroLEOneClass α] [CovariantClass α α (·+·) (·≤·)] :
  (0 : α) ≤ 3 := by
  rw [← two_add_one_eq_three]
  exact add_nonneg zero_le_two zero_le_one

lemma zero_le_four [Preorder α] [ZeroLEOneClass α] [CovariantClass α α (·+·) (·≤·)] :
    (0 : α) ≤ 4 := by
  rw [← three_add_one_eq_four]
  exact add_nonneg zero_le_three zero_le_one

lemma one_le_two [LE α] [ZeroLEOneClass α] [CovariantClass α α (·+·) (·≤·)] :
  (1 : α) ≤ 2 :=
calc 1 = 1 + 0 := (add_zero 1).symm
     _ ≤ 1 + 1 := add_le_add_left zero_le_one _
     _ = 2 := one_add_one_eq_two

lemma one_le_two' [LE α] [ZeroLEOneClass α] [CovariantClass α α (swap (·+·)) (·≤·)] :
  (1 : α) ≤ 2 :=
calc 1 = 0 + 1 := (zero_add 1).symm
     _ ≤ 1 + 1 := add_le_add_right zero_le_one _
     _ = 2 := one_add_one_eq_two

section
variable [PartialOrder α] [ZeroLEOneClass α] [NeZero (1 : α)]

section
variable [CovariantClass α α (·+·) (·≤·)]

/-- See `zero_lt_two'` for a version with the type explicit. -/
@[simp] lemma zero_lt_two : (0 : α) < 2 := zero_lt_one.trans_le one_le_two
/-- See `zero_lt_three'` for a version with the type explicit. -/
@[simp] lemma zero_lt_three : (0 : α) < 3 := by
  rw [← two_add_one_eq_three]
  exact lt_add_of_lt_of_nonneg zero_lt_two zero_le_one
/-- See `zero_lt_four'` for a version with the type explicit. -/
@[simp] lemma zero_lt_four : (0 : α) < 4 := by
  rw [← three_add_one_eq_four]
  exact lt_add_of_lt_of_nonneg zero_lt_three zero_le_one

variable (α)

/-- See `zero_lt_two` for a version with the type implicit. -/
lemma zero_lt_two' : (0 : α) < 2 := zero_lt_two
/-- See `zero_lt_three` for a version with the type implicit. -/
lemma zero_lt_three' : (0 : α) < 3 := zero_lt_three
/-- See `zero_lt_four` for a version with the type implicit. -/
lemma zero_lt_four' : (0 : α) < 4 := zero_lt_four

instance zero_le_one_class.ne_zero.two : NeZero (2 : α) := ⟨zero_lt_two.ne'⟩
instance zero_le_one_class.ne_zero.three : NeZero (3 : α) := ⟨zero_lt_three.ne'⟩
instance zero_le_one_class.ne_zero.four : NeZero (4 : α) := ⟨zero_lt_four.ne'⟩

end

lemma one_lt_two [CovariantClass α α (·+·) (·<·)] : (1 : α) < 2 := by
  rw [← one_add_one_eq_two]
  exact lt_add_one _

end

alias zero_lt_two ← two_pos
alias zero_lt_three ← three_pos
alias zero_lt_four ← four_pos
