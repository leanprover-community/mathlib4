/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Yury Kudryashov
-/
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Units.Basic

/-!
# Definitions of group actions

This file defines a hierarchy of group action type-classes on top of the previously defined
notation classes `SMul` and its additive version `VAdd`:

* `MulAction M α` and its additive version `AddAction G P` are typeclasses used for
  actions of multiplicative and additive monoids and groups; they extend notation classes
  `SMul` and `VAdd` that are defined in `Algebra.Group.Defs`;
* `DistribMulAction M A` is a typeclass for an action of a multiplicative monoid on
  an additive monoid such that `a • (b + c) = a • b + a • c` and `a • 0 = 0`.

The hierarchy is extended further by `Module`, defined elsewhere.

Also provided are typeclasses for faithful and transitive actions, and typeclasses regarding the
interaction of different group actions,

* `SMulCommClass M N α` and its additive version `VAddCommClass M N α`;
* `IsScalarTower M N α` and its additive version `VAddAssocClass M N α`;
* `IsCentralScalar M α` and its additive version `IsCentralVAdd M N α`.

## Notation

- `a • b` is used as notation for `SMul.smul a b`.
- `a +ᵥ b` is used as notation for `VAdd.vadd a b`.

## Implementation details

This file should avoid depending on other parts of `GroupTheory`, to avoid import cycles.
More sophisticated lemmas belong in `GroupTheory.GroupAction`.

## Tags

group action
-/

assert_not_exists RelIso Equiv.Perm.equivUnitsEnd Prod.fst_mul Ring

open Function

variable {G G₀ A B M M₀ N₀ R α : Type*}

section SMulZeroClass
variable [Zero A] [Zero B] [SMulZeroClass M A] [SMul M B]

/-- Pullback a zero-preserving scalar multiplication along an injective zero-preserving map.
See note [reducible non-instances]. -/
protected abbrev Function.Injective.smulZeroClass (f : ZeroHom B A)
    (hf : Injective f) (smul : ∀ (c : M) (x), f (c • x) = c • f x) :
    SMulZeroClass M B where
  smul := (· • ·)
  smul_zero c := hf <| by simp only [smul, map_zero, smul_zero]

/-- Pushforward a zero-preserving scalar multiplication along a zero-preserving map.
See note [reducible non-instances]. -/
protected abbrev ZeroHom.smulZeroClass [Zero B] [SMul M B] (f : ZeroHom A B)
    (smul : ∀ (c : M) (x), f (c • x) = c • f x) :
    SMulZeroClass M B where
  -- Porting note: `simp` no longer works here.
  smul_zero c := by rw [← map_zero f, ← smul, smul_zero]

variable (A) in
/-- Each element of the scalars defines a zero-preserving map. -/
@[simps]
def SMulZeroClass.toZeroHom (x : M) : ZeroHom A A where
  toFun := (x • ·)
  map_zero' := smul_zero x

end SMulZeroClass

section GroupWithZero
variable [GroupWithZero G₀] [MulAction G₀ α] {a : G₀}

protected lemma MulAction.bijective₀ (ha : a ≠ 0) : Bijective (a • · : α → α) :=
  MulAction.bijective <| Units.mk0 a ha

protected lemma MulAction.injective₀ (ha : a ≠ 0) : Injective (a • · : α → α) :=
  (MulAction.bijective₀ ha).injective

protected lemma MulAction.surjective₀ (ha : a ≠ 0) : Surjective (a • · : α → α) :=
  (MulAction.bijective₀ ha).surjective

end GroupWithZero

section DistribSMul
variable [AddZeroClass A] [DistribSMul M A]

variable (A) in
/-- Each element of the scalars defines an additive monoid homomorphism. -/
@[simps]
def DistribSMul.toAddMonoidHom (x : M) : A →+ A :=
  { SMulZeroClass.toZeroHom A x with toFun := (x • ·), map_add' := smul_add x }

end DistribSMul

section DistribMulAction
variable [Group G] [Monoid M] [AddMonoid A]
variable (A)

/-- Each element of the group defines an additive monoid isomorphism.

This is a stronger version of `MulAction.toPerm`. -/
@[simps (config := { simpRhs := true })]
def DistribMulAction.toAddEquiv [DistribMulAction G A] (x : G) : A ≃+ A where
  __ := DistribSMul.toAddMonoidHom A x
  __ := MulAction.toPerm x

end DistribMulAction

lemma IsUnit.smul_sub_iff_sub_inv_smul [Group G] [Monoid R] [AddGroup R] [DistribMulAction G R]
    [IsScalarTower G R R] [SMulCommClass G R R] (r : G) (a : R) :
    IsUnit (r • (1 : R) - a) ↔ IsUnit (1 - r⁻¹ • a) := by
  rw [← isUnit_smul_iff r (1 - r⁻¹ • a), smul_sub, smul_inv_smul]
