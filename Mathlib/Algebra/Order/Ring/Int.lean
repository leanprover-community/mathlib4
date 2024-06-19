/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
import Mathlib.Algebra.Ring.Int
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Ring.Defs

#align_import data.int.order.basic from "leanprover-community/mathlib"@"e8638a0fcaf73e4500469f368ef9494e495099b3"

/-!
# The integers form a linear ordered ring

This file contains:
* instances on `ℤ`. The stronger one is `Int.instLinearOrderedCommRing`.
* basic lemmas about integers that involve order properties.

## Recursors

* `Int.rec`: Sign disjunction. Something is true/defined on `ℤ` if it's true/defined for nonnegative
  and for negative values. (Defined in core Lean 3)
* `Int.inductionOn`: Simple growing induction on positive numbers, plus simple decreasing induction
  on negative numbers. Note that this recursor is currently only `Prop`-valued.
* `Int.inductionOn'`: Simple growing induction for numbers greater than `b`, plus simple decreasing
  induction on numbers less than `b`.
-/

open Function Nat

namespace Int

instance instLinearOrderedCommRing : LinearOrderedCommRing ℤ where
  __ := instCommRing
  __ := instLinearOrder
  add_le_add_left := @Int.add_le_add_left
  mul_pos := @Int.mul_pos
  zero_le_one := le_of_lt Int.zero_lt_one

/-!
### Extra instances to short-circuit type class resolution

These also prevent non-computable instances being used to construct these instances non-computably.
-/

instance instOrderedCommRing : OrderedCommRing ℤ := StrictOrderedCommRing.toOrderedCommRing'
instance instOrderedRing : OrderedRing ℤ := StrictOrderedRing.toOrderedRing'

/-! ### Miscellaneous lemmas -/

lemma _root_.Nat.cast_natAbs {α : Type*} [AddGroupWithOne α] (n : ℤ) : (n.natAbs : α) = |n| := by
  rw [← natCast_natAbs, Int.cast_natCast]
#align nat.cast_nat_abs Nat.cast_natAbs

/-- Note this holds in marginally more generality than `Int.cast_mul` -/
lemma cast_mul_eq_zsmul_cast {α : Type*} [AddCommGroupWithOne α] :
    ∀ m n : ℤ, ↑(m * n) = m • (n : α) :=
  fun m ↦ Int.induction_on m (by simp) (fun _ ih ↦ by simp [add_mul, add_zsmul, ih]) fun _ ih ↦ by
    simp only [sub_mul, one_mul, cast_sub, ih, sub_zsmul, one_zsmul, ← sub_eq_add_neg, forall_const]
#align int.cast_mul_eq_zsmul_cast Int.cast_mul_eq_zsmul_cast

end Int

section bit0_bit1
variable {R}
set_option linter.deprecated false

-- The next four lemmas allow us to replace multiplication by a numeral with a `zsmul` expression.

section NonUnitalNonAssocRing
variable [NonUnitalNonAssocRing R] (n r : R)

lemma bit0_mul : bit0 n * r = (2 : ℤ) • (n * r) := by
  rw [bit0, add_mul, ← one_add_one_eq_two, add_zsmul, one_zsmul]
#align bit0_mul bit0_mul

lemma mul_bit0 : r * bit0 n = (2 : ℤ) • (r * n) := by
  rw [bit0, mul_add, ← one_add_one_eq_two, add_zsmul, one_zsmul]
#align mul_bit0 mul_bit0

end NonUnitalNonAssocRing

section NonAssocRing
variable [NonAssocRing R] (n r : R)

lemma bit1_mul : bit1 n * r = (2 : ℤ) • (n * r) + r := by rw [bit1, add_mul, bit0_mul, one_mul]
#align bit1_mul bit1_mul

lemma mul_bit1 {n r : R} : r * bit1 n = (2 : ℤ) • (r * n) + r := by
  rw [bit1, mul_add, mul_bit0, mul_one]
#align mul_bit1 mul_bit1

end NonAssocRing
end bit0_bit1

-- We should need only a minimal development of sets in order to get here.
assert_not_exists Set.range
