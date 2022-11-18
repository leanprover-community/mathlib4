/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Gabriel Ebner
-/
import Mathlib.Data.Nat.Cast.Defs

/-!
# Cast of integers

This file defines the *canonical* homomorphism from the integers into an
additive group with a one (typically a `Ring`).  In additive groups with a one
element, there exists a unique such homomorphism and we store it in the
`intCast : ℤ → R` field.

Preferentially, the homomorphism is written as a coercion.

## Main declarations

* `Int.cast`: Canonical homomorphism `ℤ → R`.
* `AddGroupWithOne`: Type class for `Int.cast`.
-/


universe u

--attribute [simp] Int.ofNat_eq_coe

/-- Default value for `IntCast.intCast` in an `AddGroupWithOne`. -/
protected def Int.castDef {R : Type u} [NatCast R] [Neg R] : ℤ → R
  | (n : ℕ) => n
  | Int.negSucc n => -(n + 1 : ℕ)
#align int.cast_def Int.castDef

/-- Type class for the canonical homomorphism `ℤ → R`.
-/
class IntCast (R : Type u) where
  intCast : ℤ → R
#align has_int_cast IntCast

/-! ### Additive groups with one -/

class AddGroupWithOne (R : Type u) extends IntCast R, AddMonoidWithOne R, AddGroup R where
  intCast := Int.castDef
  intCast_ofNat : ∀ n : ℕ, intCast (n : ℕ) = Nat.cast n := by intros; rfl
  intCast_negSucc : ∀ n : ℕ, intCast (Int.negSucc n) = - Nat.cast (n + 1) := by intros; rfl
#align add_group_with_one AddGroupWithOne
#align add_group_with_one.to_int_cast AddGroupWithOne.toIntCast
#align add_group_with_one.to_add_monoid_with_one AddGroupWithOne.toAddMonoidWithOne
#align add_group_with_one.to_add_group AddGroupWithOne.toAddGroup
#align add_group_with_one.int_cast_of_nat AddGroupWithOne.intCast_ofNat
#align add_group_with_one.int_cast_neg_succ_of_nat AddGroupWithOne.intCast_negSucc

namespace Int

/-- Canonical homomorphism from the integers to any ring(-like) structure `R` -/
@[coe] def cast [IntCast R] : ℤ → R := IntCast.intCast
#align int.cast Int.cast

instance [IntCast R] : CoeTail ℤ R where coe := cast

@[simp high, nolint simpNF] -- this lemma competes with `Int.ofNat_eq_cast` to come later
theorem cast_ofNat [AddGroupWithOne R] : (cast (ofNat n) : R) = Nat.cast n :=
  AddGroupWithOne.intCast_ofNat _
#align int.cast_coe_nat Int.cast_ofNat

@[simp, norm_cast]
theorem cast_negSucc [AddGroupWithOne R] : (cast (negSucc n) : R) = (-(Nat.cast (n + 1)) : R) :=
  AddGroupWithOne.intCast_negSucc _
#align int.cast_neg_succ_of_nat Int.cast_negSucc

@[simp, norm_cast] theorem cast_zero [AddGroupWithOne R] : ((0 : ℤ) : R) = 0 := by
  erw [cast_ofNat, Nat.cast_zero]
@[simp, norm_cast] theorem cast_one [AddGroupWithOne R] : ((1 : ℤ) : R) = 1 := by
  erw [cast_ofNat, Nat.cast_one]

end Int

/-- An `AddCommGroupWithOne` is an `AddGroupWithOne` satisfying `a + b = b + a`. -/
class AddCommGroupWithOne (R : Type u) extends AddCommGroup R, AddGroupWithOne R
#align add_comm_group_with_one AddCommGroupWithOne

open Nat
