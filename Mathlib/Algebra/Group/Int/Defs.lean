/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
module

public import Mathlib.Algebra.Group.Defs

/-!
# The integers form a group

This file contains the additive group and multiplicative monoid instances on the integers.

See note [foundational algebra order theory].
-/

@[expose] public section

assert_not_exists Ring DenselyOrdered

open Nat

namespace Int

/-! ### Instances -/

instance instCommMonoid : CommMonoid ℤ where
  mul_comm := Int.mul_comm
  mul_one := Int.mul_one
  one_mul := Int.one_mul
  npow n x := x ^ n
  npow_zero _ := by simp [Int.pow_zero]
  npow_succ _ _ := by simp [Int.pow_succ]
  mul_assoc := Int.mul_assoc

instance instAddCommGroup : AddCommGroup ℤ where
  add_comm := Int.add_comm
  add_assoc := Int.add_assoc
  add_zero := Int.add_zero
  zero_add := Int.zero_add
  neg_add_cancel := Int.add_left_neg
  nsmul := (·*·)
  nsmul_zero := Int.zero_mul
  nsmul_succ n x :=
    show (n + 1 : ℤ) * x = n * x + x
    by rw [Int.add_mul, Int.one_mul]
  zsmul := (·*·)
  zsmul_zero' := Int.zero_mul
  zsmul_succ' m n := by
    simp only [natCast_succ, Int.add_mul, Int.add_comm, Int.one_mul]
  zsmul_neg' m n := by simp only [negSucc_eq, natCast_succ, Int.neg_mul]
  sub_eq_add_neg _ _ := Int.sub_eq_add_neg

-- Thise instance can also be found from the `LinearOrderedCommMonoidWithZero ℤ` instance by
-- typeclass search, but it is better practice to not rely on algebraic order theory to prove
-- purely algebraic results on concrete types. Eg the results can be made available earlier.

instance instIsAddTorsionFree : IsAddTorsionFree ℤ where
  nsmul_right_injective _n hn _x _y := Int.eq_of_mul_eq_mul_left (by cutsat)

/-!
### Extra instances to short-circuit type class resolution

These also prevent non-computable instances like `Int.instNormedCommRing` being used to construct
these instances non-computably.
-/

set_option linter.style.commandStart false

instance instAddCommMonoid    : AddCommMonoid ℤ    := by infer_instance
instance instAddMonoid        : AddMonoid ℤ        := by infer_instance
instance instMonoid           : Monoid ℤ           := by infer_instance
instance instCommSemigroup    : CommSemigroup ℤ    := by infer_instance
instance instSemigroup        : Semigroup ℤ        := by infer_instance
instance instAddGroup         : AddGroup ℤ         := by infer_instance
instance instAddCommSemigroup : AddCommSemigroup ℤ := by infer_instance
instance instAddSemigroup     : AddSemigroup ℤ     := by infer_instance

-- This lemma is higher priority than later `_root_.nsmul_eq_mul` so that the `simpNF` is happy
@[simp high] protected lemma nsmul_eq_mul (n : ℕ) (a : ℤ) : n • a = n * a := rfl

-- This lemma is higher priority than later `_root_.zsmul_eq_mul` so that the `simpNF` is happy
@[simp high] protected lemma zsmul_eq_mul (n a : ℤ) : n • a = n * a := rfl

end Int

-- TODO: Do we really need this lemma? This is just `smul_eq_mul`
lemma zsmul_int_int (a b : ℤ) : a • b = a * b := rfl

lemma zsmul_int_one (n : ℤ) : n • (1 : ℤ) = n := mul_one _
