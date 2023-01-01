/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen

! This file was ported from Lean 3 source module data.int.absolute_value
! leanprover-community/mathlib commit 9aba7801eeecebb61f58a5763c2b6dd1b47dc6ef
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Module.Basic
import Mathbin.Algebra.Order.AbsoluteValue
import Mathbin.Data.Int.Cast.Lemmas
import Mathbin.Data.Int.Units
import Mathbin.GroupTheory.GroupAction.Units

/-!
# Absolute values and the integers

This file contains some results on absolute values applied to integers.

## Main results

 * `absolute_value.map_units_int`: an absolute value sends all units of `ℤ` to `1`
 * `int.nat_abs_hom`: `int.nat_abs` bundled as a `monoid_with_zero_hom`
-/


variable {R S : Type _} [Ring R] [LinearOrderedCommRing S]

@[simp]
theorem AbsoluteValue.map_units_int (abv : AbsoluteValue ℤ S) (x : ℤˣ) : abv x = 1 := by
  rcases Int.units_eq_one_or x with (rfl | rfl) <;> simp
#align absolute_value.map_units_int AbsoluteValue.map_units_int

@[simp]
theorem AbsoluteValue.map_units_int_cast [Nontrivial R] (abv : AbsoluteValue R S) (x : ℤˣ) :
    abv ((x : ℤ) : R) = 1 := by rcases Int.units_eq_one_or x with (rfl | rfl) <;> simp
#align absolute_value.map_units_int_cast AbsoluteValue.map_units_int_cast

@[simp]
theorem AbsoluteValue.map_units_int_smul (abv : AbsoluteValue R S) (x : ℤˣ) (y : R) :
    abv (x • y) = abv y := by rcases Int.units_eq_one_or x with (rfl | rfl) <;> simp
#align absolute_value.map_units_int_smul AbsoluteValue.map_units_int_smul

/-- `int.nat_abs` as a bundled monoid with zero hom. -/
@[simps]
def Int.natAbsHom : ℤ →*₀ ℕ where
  toFun := Int.natAbs
  map_mul' := Int.natAbs_mul
  map_one' := Int.natAbs_one
  map_zero' := Int.natAbs_zero
#align int.nat_abs_hom Int.natAbsHom

