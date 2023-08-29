/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl, Yuyang Zhao
-/
import Mathlib.Algebra.Order.Monoid.Lemmas
import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.Data.Nat.Cast.Defs

#align_import algebra.order.monoid.nat_cast from "leanprover-community/mathlib"@"07fee0ca54c320250c98bacf31ca5f288b2bcbe2"

/-!
# Order of numerals in an `AddMonoidWithOne`.
-/

variable {α : Type*}

open Function

lemma lt_add_one [One α] [AddZeroClass α] [PartialOrder α] [ZeroLEOneClass α]
  [NeZero (1 : α)] [CovariantClass α α (·+·) (·<·)] (a : α) : a < a + 1 :=
lt_add_of_pos_right _ zero_lt_one
#align lt_add_one lt_add_one

lemma lt_one_add [One α] [AddZeroClass α] [PartialOrder α] [ZeroLEOneClass α]
  [NeZero (1 : α)] [CovariantClass α α (swap (·+·)) (·<·)] (a : α) : a < 1 + a :=
lt_add_of_pos_left _ zero_lt_one
#align lt_one_add lt_one_add

variable [AddMonoidWithOne α]

lemma zero_le_two [Preorder α] [ZeroLEOneClass α] [CovariantClass α α (·+·) (·≤·)] :
    (0 : α) ≤ 2 := by
  rw [← one_add_one_eq_two]
  -- ⊢ 0 ≤ 1 + 1
  exact add_nonneg zero_le_one zero_le_one
  -- 🎉 no goals
#align zero_le_two zero_le_two

lemma zero_le_three [Preorder α] [ZeroLEOneClass α] [CovariantClass α α (·+·) (·≤·)] :
  (0 : α) ≤ 3 := by
  rw [← two_add_one_eq_three]
  -- ⊢ 0 ≤ 2 + 1
  exact add_nonneg zero_le_two zero_le_one
  -- 🎉 no goals
#align zero_le_three zero_le_three

lemma zero_le_four [Preorder α] [ZeroLEOneClass α] [CovariantClass α α (·+·) (·≤·)] :
    (0 : α) ≤ 4 := by
  rw [← three_add_one_eq_four]
  -- ⊢ 0 ≤ 3 + 1
  exact add_nonneg zero_le_three zero_le_one
  -- 🎉 no goals
#align zero_le_four zero_le_four

lemma one_le_two [LE α] [ZeroLEOneClass α] [CovariantClass α α (·+·) (·≤·)] :
  (1 : α) ≤ 2 :=
calc (1 : α) = 1 + 0 := (add_zero 1).symm
     _ ≤ 1 + 1 := add_le_add_left zero_le_one _
     _ = 2 := one_add_one_eq_two
#align one_le_two one_le_two

lemma one_le_two' [LE α] [ZeroLEOneClass α] [CovariantClass α α (swap (·+·)) (·≤·)] :
  (1 : α) ≤ 2 :=
calc (1 : α) = 0 + 1 := (zero_add 1).symm
     _ ≤ 1 + 1 := add_le_add_right zero_le_one _
     _ = 2 := one_add_one_eq_two
#align one_le_two' one_le_two'

section
variable [PartialOrder α] [ZeroLEOneClass α] [NeZero (1 : α)]

section
variable [CovariantClass α α (·+·) (·≤·)]

/-- See `zero_lt_two'` for a version with the type explicit. -/
@[simp] lemma zero_lt_two : (0 : α) < 2 := zero_lt_one.trans_le one_le_two
#align zero_lt_two zero_lt_two

/-- See `zero_lt_three'` for a version with the type explicit. -/
@[simp] lemma zero_lt_three : (0 : α) < 3 := by
  rw [← two_add_one_eq_three]
  -- ⊢ 0 < 2 + 1
  exact lt_add_of_lt_of_nonneg zero_lt_two zero_le_one
  -- 🎉 no goals
#align zero_lt_three zero_lt_three

/-- See `zero_lt_four'` for a version with the type explicit. -/
@[simp] lemma zero_lt_four : (0 : α) < 4 := by
  rw [← three_add_one_eq_four]
  -- ⊢ 0 < 3 + 1
  exact lt_add_of_lt_of_nonneg zero_lt_three zero_le_one
  -- 🎉 no goals
#align zero_lt_four zero_lt_four

variable (α)

/-- See `zero_lt_two` for a version with the type implicit. -/
lemma zero_lt_two' : (0 : α) < 2 := zero_lt_two
#align zero_lt_two' zero_lt_two'

/-- See `zero_lt_three` for a version with the type implicit. -/
lemma zero_lt_three' : (0 : α) < 3 := zero_lt_three
#align zero_lt_three' zero_lt_three'

/-- See `zero_lt_four` for a version with the type implicit. -/
lemma zero_lt_four' : (0 : α) < 4 := zero_lt_four
#align zero_lt_four' zero_lt_four'

instance ZeroLEOneClass.neZero.two : NeZero (2 : α) := ⟨zero_lt_two.ne'⟩
instance ZeroLEOneClass.neZero.three : NeZero (3 : α) := ⟨zero_lt_three.ne'⟩
instance ZeroLEOneClass.neZero.four : NeZero (4 : α) := ⟨zero_lt_four.ne'⟩

end

lemma one_lt_two [CovariantClass α α (·+·) (·<·)] : (1 : α) < 2 := by
  rw [← one_add_one_eq_two]
  -- ⊢ 1 < 1 + 1
  exact lt_add_one _
  -- 🎉 no goals
#align one_lt_two one_lt_two

end

alias two_pos := zero_lt_two
#align two_pos two_pos

alias three_pos := zero_lt_three
#align three_pos three_pos

alias four_pos := zero_lt_four
#align four_pos four_pos
