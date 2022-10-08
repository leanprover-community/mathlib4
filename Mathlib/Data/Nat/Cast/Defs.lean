/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Gabriel Ebner
-/
import Mathlib.Algebra.Group.Basic

/-!
# Cast of natural numbers

This file defines the *canonical* homomorphism from the natural numbers into an
`AddMonoid` with a one.  In additive monoids with one, there exists a unique
such homomorphism and we store it in the `natCast : ℕ → R` field.

Preferentially, the homomorphism is written as a coercion.

## Main declarations

* `AddMonoidWithOne`: Type class for `Nat.cast`.
* `Nat.cast`: Canonical homomorphism `ℕ → R`.
-/


universe u

/-- The numeral `((0+1)+⋯)+1`. -/
protected def Nat.unaryCast {R : Type u} [One R] [Zero R] [Add R] : ℕ → R
  | 0 => 0
  | n + 1 => Nat.unaryCast n + 1

/-- Type class for the canonical homomorphism `ℕ → R`.
-/
class HasNatCast (R : Type u) where
  natCast : ℕ → R

/-- An `AddMonoidWithOne` is an `AddMonoid` with a `1`.
It also contains data for the unique homomorphism `ℕ → R`.
-/
class AddMonoidWithOne (R : Type u) extends HasNatCast R, AddMonoid R, One R where
  natCast := Nat.unaryCast
  nat_cast_zero : natCast 0 = (0 : R) := by
    intros
    rfl
  nat_cast_succ : ∀ n, natCast (n + 1) = (natCast n + 1 : R) := by
    intros
    rfl

/-- Canonical homomorphism from `ℕ` to a additive monoid `R` with a `1`. -/
protected def Nat.cast {R : Type u} [HasNatCast R] : ℕ → R :=
  HasNatCast.natCast

/-- An `AddCommMonoidWithOne` is an `AddMonoidWithOne` satisfying `a + b = b + a`.  -/
class AddCommMonoidWithOne (R : Type _) extends AddMonoidWithOne R, AddCommMonoid R
