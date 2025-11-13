/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.GroupWithZero.Action.End
import Mathlib.Algebra.Ring.Hom.Defs

/-!
# Group action on rings

This file defines the typeclass of monoid acting on semirings `MulSemiringAction M R`.

An example of a `MulSemiringAction` is the action of the Galois group `Gal(L/K)` on
the big field `L`. Note that `Algebra` does not in general satisfy the axioms
of `MulSemiringAction`.

## Implementation notes

There is no separate typeclass for group acting on rings, group acting on fields, etc.
They are all grouped under `MulSemiringAction`.

## Note

The corresponding typeclass of subrings invariant under such an action, `IsInvariantSubring`, is
defined in `Mathlib/Algebra/Ring/Action/Invariant.lean`.

## Tags

group action

-/

assert_not_exists Equiv.Perm.equivUnitsEnd Prod.fst_mul

universe u v

/-- Typeclass for multiplicative actions by monoids on semirings.

This combines `DistribMulAction` with `MulDistribMulAction`: it expresses
the interplay between the action and both addition and multiplication on the target.
Two key axioms are `g • (x + y) = (g • x) + (g • y)` and `g • (x * y) = (g • x) * (g • y)`.

A typical use case is the action of a Galois group $Gal(L/K)$ on the field `L`.
-/
class MulSemiringAction (M : Type u) (R : Type v) [Monoid M] [Semiring R] extends
  DistribMulAction M R where
  /-- Multiplying `1` by a scalar gives `1` -/
  smul_one : ∀ g : M, (g • (1 : R) : R) = 1
  /-- Scalar multiplication distributes across multiplication -/
  smul_mul : ∀ (g : M) (x y : R), g • (x * y) = g • x * g • y

section Semiring

variable (M N : Type*) [Monoid M] [Monoid N]
variable (R : Type v) [Semiring R]

-- note we could not use `extends` since these typeclasses are made with `old_structure_cmd`
instance (priority := 100) MulSemiringAction.toMulDistribMulAction
    (M R) {_ : Monoid M} {_ : Semiring R} [h : MulSemiringAction M R] :
    MulDistribMulAction M R :=
  { h with }

/-- Each element of the monoid defines a semiring homomorphism. -/
@[simps!]
def MulSemiringAction.toRingHom [MulSemiringAction M R] (x : M) : R →+* R :=
  { MulDistribMulAction.toMonoidHom R x, DistribMulAction.toAddMonoidHom R x with }

theorem toRingHom_injective [MulSemiringAction M R] [FaithfulSMul M R] :
    Function.Injective (MulSemiringAction.toRingHom M R) := fun _ _ h =>
  eq_of_smul_eq_smul fun r => RingHom.ext_iff.1 h r

/-- The tautological action by `R →+* R` on `R`.

This generalizes `Function.End.applyMulAction`. -/
instance RingHom.applyMulSemiringAction : MulSemiringAction (R →+* R) R where
  smul := (· <| ·)
  smul_one := map_one
  smul_mul := map_mul
  smul_zero := RingHom.map_zero
  smul_add := RingHom.map_add
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[simp]
protected theorem RingHom.smul_def (f : R →+* R) (a : R) : f • a = f a :=
  rfl

/-- `RingHom.applyMulSemiringAction` is faithful. -/
instance RingHom.applyFaithfulSMul : FaithfulSMul (R →+* R) R :=
  ⟨fun {_ _} h => RingHom.ext h⟩

section

variable {M N}

/-- Compose a `MulSemiringAction` with a `MonoidHom`, with action `f r' • m`.
See note [reducible non-instances]. -/
abbrev MulSemiringAction.compHom (f : N →* M) [MulSemiringAction M R] : MulSemiringAction N R :=
  { DistribMulAction.compHom R f, MulDistribMulAction.compHom R f with }

end

section SimpLemmas

attribute [simp] smul_one smul_mul' smul_zero smul_add

end SimpLemmas

end Semiring
