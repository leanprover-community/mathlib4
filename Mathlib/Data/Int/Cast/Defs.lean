/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Gabriel Ebner
-/
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Util.NoInstances

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

/-! ### Additive groups with one -/

no_instances
/-- An `AddGroupWithOne` is an `AddGroup` with a 1. It also contains data for the unique
homomorphisms `ℕ → R` and `ℤ → R`. -/
class AddGroupWithOne (R : Type u) extends AddGroup R, AddMonoidWithOne R, IntCast R where
  /-- The canonical homomorphism `ℤ → R`. -/
  intCast := Int.castDef
  /-- The canonical homomorphism `ℤ → R` agrees with the one from `ℕ → R` on `ℕ`. -/
  intCast_ofNat : ∀ n : ℕ, intCast (n : ℕ) = Nat.cast n := by intros; rfl
  /-- The canonical homomorphism `ℤ → R` for negative values is just the negation of the values
  of the canonical homomorphism `ℕ → R`. -/
  intCast_negSucc : ∀ n : ℕ, intCast (Int.negSucc n) = - Nat.cast (n + 1) := by intros; rfl

attribute [instance] AddGroupWithOne.toIntCast
attribute [instance] AddGroupWithOne.toAddMonoidWithOne
attribute [instance] AddGroupWithOne.toAddGroup

no_instances
/-- An `AddCommGroupWithOne` is an `AddGroupWithOne` satisfying `a + b = b + a`. -/
class AddCommGroupWithOne (R : Type u)
  extends AddGroupWithOne R, AddCommGroup R, AddCommMonoidWithOne R

attribute [instance] AddCommGroupWithOne.toAddCommGroup
attribute [instance] AddCommGroupWithOne.toAddGroupWithOne
attribute [instance] AddCommGroupWithOne.toAddCommMonoidWithOne
