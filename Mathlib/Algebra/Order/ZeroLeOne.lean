/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Mathbin.Algebra.Group.Defs
import Mathbin.Algebra.CovariantAndContravariant
import Mathbin.Algebra.Order.Monoid.Lemmas

/-!
# Typeclass expressing `0 ≤ 1`.
-/


variable {α : Type _}

open Function

/-- Typeclass for expressing that the `0` of a type is less or equal to its `1`. -/
class ZeroLeOneClass (α : Type _) [Zero α] [One α] [LE α] where
  zero_le_one : (0 : α) ≤ 1
#align zero_le_one_class ZeroLeOneClass

@[simp]
theorem zero_le_one [Zero α] [One α] [LE α] [ZeroLeOneClass α] : (0 : α) ≤ 1 :=
  ZeroLeOneClass.zero_le_one
#align zero_le_one zero_le_one

-- `zero_le_one` with an explicit type argument.
theorem zero_le_one' (α) [Zero α] [One α] [LE α] [ZeroLeOneClass α] : (0 : α) ≤ 1 :=
  zero_le_one
#align zero_le_one' zero_le_one'

theorem zero_le_two [Preorder α] [One α] [AddZeroClass α] [ZeroLeOneClass α] [CovariantClass α α (· + ·) (· ≤ ·)] :
    (0 : α) ≤ 2 :=
  add_nonneg zero_le_one zero_le_one
#align zero_le_two zero_le_two

theorem zero_le_three [Preorder α] [One α] [AddZeroClass α] [ZeroLeOneClass α] [CovariantClass α α (· + ·) (· ≤ ·)] :
    (0 : α) ≤ 3 :=
  add_nonneg zero_le_two zero_le_one
#align zero_le_three zero_le_three

theorem zero_le_four [Preorder α] [One α] [AddZeroClass α] [ZeroLeOneClass α] [CovariantClass α α (· + ·) (· ≤ ·)] :
    (0 : α) ≤ 4 :=
  add_nonneg zero_le_two zero_le_two
#align zero_le_four zero_le_four

theorem one_le_two [LE α] [One α] [AddZeroClass α] [ZeroLeOneClass α] [CovariantClass α α (· + ·) (· ≤ ·)] :
    (1 : α) ≤ 2 :=
  calc
    1 = 1 + 0 := (add_zero 1).symm
    _ ≤ 1 + 1 := add_le_add_left zero_le_one _
    
#align one_le_two one_le_two

theorem one_le_two' [LE α] [One α] [AddZeroClass α] [ZeroLeOneClass α] [CovariantClass α α (swap (· + ·)) (· ≤ ·)] :
    (1 : α) ≤ 2 :=
  calc
    1 = 0 + 1 := (zero_add 1).symm
    _ ≤ 1 + 1 := add_le_add_right zero_le_one _
    
#align one_le_two' one_le_two'

