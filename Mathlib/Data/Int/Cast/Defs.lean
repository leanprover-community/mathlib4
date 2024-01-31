/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Gabriel Ebner
-/
import Mathlib.Data.Nat.Cast.Defs

#align_import data.int.cast.defs from "leanprover-community/mathlib"@"acebd8d49928f6ed8920e502a6c90674e75bd441"

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

/-- Default value for `IntCast.intCast` in an `AddGroupWithOne`. -/
protected def Int.castDef {R : Type u} [NatCast R] [Neg R] : ℤ → R
  | (n : ℕ) => n
  | Int.negSucc n => -(n + 1 : ℕ)
#align int.cast_def Int.castDef

#align has_int_cast IntCast
#align int.cast Int.cast

/-! ### Additive groups with one -/

/-- An `AddGroupWithOne` is an `AddGroup` with a 1. It also contains data for the unique
homomorphisms `ℕ → R` and `ℤ → R`. -/
class AddGroupWithOne (R : Type u) extends IntCast R, AddMonoidWithOne R, AddGroup R where
  /-- The canonical homomorphism `ℤ → R`. -/
  intCast := Int.castDef
  /-- The canonical homomorphism `ℤ → R` agrees with the one from `ℕ → R` on `ℕ`. -/
  intCast_ofNat : ∀ n : ℕ, intCast (n : ℕ) = Nat.cast n := by intros; rfl
  /-- The canonical homomorphism `ℤ → R` for negative values is just the negation of the values
  of the canonical homomorphism `ℕ → R`. -/
  intCast_negSucc : ∀ n : ℕ, intCast (Int.negSucc n) = - Nat.cast (n + 1) := by intros; rfl
#align add_group_with_one AddGroupWithOne
#align add_group_with_one.to_int_cast AddGroupWithOne.toIntCast
#align add_group_with_one.to_add_monoid_with_one AddGroupWithOne.toAddMonoidWithOne
#align add_group_with_one.to_add_group AddGroupWithOne.toAddGroup
#align add_group_with_one.int_cast_of_nat AddGroupWithOne.intCast_ofNat
#align add_group_with_one.int_cast_neg_succ_of_nat AddGroupWithOne.intCast_negSucc

/-- An `AddCommGroupWithOne` is an `AddGroupWithOne` satisfying `a + b = b + a`. -/
class AddCommGroupWithOne (R : Type u)
  extends AddCommGroup R, AddGroupWithOne R, AddCommMonoidWithOne R
#align add_comm_group_with_one AddCommGroupWithOne
#align add_comm_group_with_one.to_add_comm_group AddCommGroupWithOne.toAddCommGroup
#align add_comm_group_with_one.to_add_group_with_one AddCommGroupWithOne.toAddGroupWithOne
#align add_comm_group_with_one.to_add_comm_monoid_with_one AddCommGroupWithOne.toAddCommMonoidWithOne
