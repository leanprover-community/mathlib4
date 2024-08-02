/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Yury Kudryashov
-/
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Group.Action.Prod
import Mathlib.Algebra.Group.Aut
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Prod
import Mathlib.Algebra.SMulWithZero

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

-- TODO:
-- assert_not_exists Ring

open Function

variable {R R' M M' N G A B α β : Type*}

section GroupWithZero
variable [GroupWithZero α] [MulAction α β] {a : α}

protected lemma MulAction.bijective₀ (ha : a ≠ 0) : Bijective (a • · : β → β) :=
  MulAction.bijective <| Units.mk0 a ha

protected lemma MulAction.injective₀ (ha : a ≠ 0) : Injective (a • · : β → β) :=
  (MulAction.bijective₀ ha).injective

protected lemma MulAction.surjective₀ (ha : a ≠ 0) : Surjective (a • · : β → β) :=
  (MulAction.bijective₀ ha).surjective

end GroupWithZero

section DistribMulAction
variable [Group G] [Monoid M] [AddMonoid A] [DistribMulAction M A]

-- Porting note: this probably is no longer relevant.
/-! Since Lean 3 does not have definitional eta for structures, we have to make sure
that the definition of `DistribMulAction.toDistribSMul` was done correctly,
and the two paths from `DistribMulAction` to `SMul` are indeed definitionally equal. -/
example :
    (DistribMulAction.toMulAction.toSMul : SMul M A) = DistribMulAction.toDistribSMul.toSMul := rfl

variable (A)

/-- Each element of the group defines an additive monoid isomorphism.

This is a stronger version of `MulAction.toPerm`. -/
@[simps (config := { simpRhs := true })]
def DistribMulAction.toAddEquiv [DistribMulAction G A] (x : G) : A ≃+ A where
  __ := toAddMonoidHom A x
  __ := MulAction.toPermHom G A x

variable (G M)

/-- Each element of the group defines an additive monoid isomorphism.

This is a stronger version of `MulAction.toPermHom`. -/
@[simps]
def DistribMulAction.toAddAut [DistribMulAction G A] : G →* AddAut A where
  toFun := toAddEquiv _
  map_one' := AddEquiv.ext (one_smul _)
  map_mul' _ _ := AddEquiv.ext (mul_smul _ _)

end DistribMulAction

/-- Scalar multiplication as a monoid homomorphism with zero. -/
@[simps]
def smulMonoidWithZeroHom {α β : Type*} [MonoidWithZero α] [MulZeroOneClass β]
    [MulActionWithZero α β] [IsScalarTower α β β] [SMulCommClass α β β] : α × β →*₀ β :=
  { smulMonoidHom with map_zero' := smul_zero _ }

section MulDistribMulAction

variable [Group α] [Monoid β] [MulDistribMulAction α β]
variable (β)

/-- Each element of the group defines a multiplicative monoid isomorphism.

This is a stronger version of `MulAction.toPerm`. -/
@[simps (config := { simpRhs := true })]
def MulDistribMulAction.toMulEquiv (x : α) : β ≃* β :=
  { MulDistribMulAction.toMonoidHom β x, MulAction.toPermHom α β x with }

variable (α)

/-- Each element of the group defines a multiplicative monoid isomorphism.

This is a stronger version of `MulAction.toPermHom`. -/
@[simps]
def MulDistribMulAction.toMulAut : α →* MulAut β where
  toFun := MulDistribMulAction.toMulEquiv β
  map_one' := MulEquiv.ext (one_smul _)
  map_mul' _ _ := MulEquiv.ext (mul_smul _ _)

variable {α β}

end MulDistribMulAction


namespace MulAut

/-- The tautological action by `MulAut M` on `M`.

This generalizes `Function.End.applyMulAction`. -/
instance applyMulDistribMulAction [Monoid M] : MulDistribMulAction (MulAut M) M where
  smul := (· <| ·)
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_one := MulEquiv.map_one
  smul_mul := MulEquiv.map_mul

end MulAut

namespace AddAut

/-- The tautological action by `AddAut A` on `A`.

This generalizes `Function.End.applyMulAction`. -/
instance applyDistribMulAction [AddMonoid A] : DistribMulAction (AddAut A) A where
  smul := (· <| ·)
  smul_zero := AddEquiv.map_zero
  smul_add := AddEquiv.map_add
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

end AddAut

section Arrow
variable [Group G] [MulAction G A] [Monoid M]

attribute [local instance] arrowAction

/-- When `M` is a monoid, `ArrowAction` is additionally a `MulDistribMulAction`. -/
def arrowMulDistribMulAction : MulDistribMulAction G (A → M) where
  smul_one _ := rfl
  smul_mul _ _ _ := rfl

attribute [local instance] arrowMulDistribMulAction

/-- Given groups `G H` with `G` acting on `A`, `G` acts by
multiplicative automorphisms on `A → H`. -/
@[simps!] def mulAutArrow : G →* MulAut (A → M) := MulDistribMulAction.toMulAut _ _

end Arrow

lemma IsUnit.smul_sub_iff_sub_inv_smul [Group G] [Monoid R] [AddGroup R] [DistribMulAction G R]
    [IsScalarTower G R R] [SMulCommClass G R R] (r : G) (a : R) :
    IsUnit (r • (1 : R) - a) ↔ IsUnit (1 - r⁻¹ • a) := by
  rw [← isUnit_smul_iff r (1 - r⁻¹ • a), smul_sub, smul_inv_smul]
