/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Order.AbsoluteValue
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.GroupTheory.GroupAction.Units

#align_import data.int.absolute_value from "leanprover-community/mathlib"@"9aba7801eeecebb61f58a5763c2b6dd1b47dc6ef"

/-!
# Absolute values and the integers

This file contains some results on absolute values applied to integers.

## Main results

 * `AbsoluteValue.map_units_int`: an absolute value sends all units of `ℤ` to `1`
 * `Int.natAbsHom`: `Int.natAbs` bundled as a `MonoidWithZeroHom`
-/


variable {R S : Type*} [Ring R] [LinearOrderedCommRing S]

@[simp]
theorem AbsoluteValue.map_units_int (abv : AbsoluteValue ℤ S) (x : ℤˣ) : abv x = 1 := by
  rcases Int.units_eq_one_or x with (rfl | rfl) <;> simp
#align absolute_value.map_units_int AbsoluteValue.map_units_int

@[simp]
theorem AbsoluteValue.map_units_intCast [Nontrivial R] (abv : AbsoluteValue R S) (x : ℤˣ) :
    abv ((x : ℤ) : R) = 1 := by rcases Int.units_eq_one_or x with (rfl | rfl) <;> simp
#align absolute_value.map_units_int_cast AbsoluteValue.map_units_intCast

@[deprecated (since := "2024-04-17")]
alias AbsoluteValue.map_units_int_cast := AbsoluteValue.map_units_intCast

@[simp]
theorem AbsoluteValue.map_units_int_smul (abv : AbsoluteValue R S) (x : ℤˣ) (y : R) :
    abv (x • y) = abv y := by rcases Int.units_eq_one_or x with (rfl | rfl) <;> simp
#align absolute_value.map_units_int_smul AbsoluteValue.map_units_int_smul

/-- `Int.natAbs` as a bundled monoid with zero hom. -/
@[simps]
def Int.natAbsHom : ℤ →*₀ ℕ where
  toFun := Int.natAbs
  map_mul' := Int.natAbs_mul
  map_one' := Int.natAbs_one
  map_zero' := Int.natAbs_zero
#align int.nat_abs_hom Int.natAbsHom
#align int.nat_abs_hom_apply Int.natAbsHom_apply
