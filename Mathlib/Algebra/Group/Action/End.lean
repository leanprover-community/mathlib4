/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Yury Kudryashov
-/
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Group.Action.Hom
import Mathlib.Algebra.Group.End

/-!
# Interaction between actions and endomorphisms/automorphisms

This file provides two things:
* The tautological actions by endomorphisms/automorphisms on their base type.
* An action by a monoid/group on a type is the same as a hom from the monoid/group to
  endomorphisms/automorphisms of the type.

## Tags

monoid action, group action
-/

assert_not_exists MonoidWithZero

open Function (Injective Surjective)

variable {G M N A α : Type*}

/-! ### Tautological actions -/

/-! #### Tautological action by `Function.End` -/

namespace Function.End

/-- The tautological action by `Function.End α` on `α`.

This is generalized to bundled endomorphisms by:
* `Equiv.Perm.applyMulAction`
* `AddMonoid.End.applyDistribMulAction`
* `AddMonoid.End.applyModule`
* `AddAut.applyDistribMulAction`
* `MulAut.applyMulDistribMulAction`
* `LinearEquiv.applyDistribMulAction`
* `LinearMap.applyModule`
* `RingHom.applyMulSemiringAction`
* `RingAut.applyMulSemiringAction`
* `AlgEquiv.applyMulSemiringAction`
* `RelHom.applyMulAction`
* `RelEmbedding.applyMulAction`
* `RelIso.applyMulAction`
-/
instance applyMulAction : MulAction (Function.End α) α where
  smul := (· <| ·)
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/-- The tautological additive action by `Additive (Function.End α)` on `α`. -/
instance applyAddAction : AddAction (Additive (Function.End α)) α := inferInstance

@[simp] lemma smul_def (f : Function.End α) (a : α) : f • a = f a := rfl

--TODO - This statement should be somethting like `toFun (f * g) = toFun f ∘ toFun g`
lemma mul_def (f g : Function.End α) : (f * g) = f ∘ g := rfl

--TODO - This statement should be somethting like `toFun 1 = id`
lemma one_def : (1 : Function.End α) = id := rfl

/-- `Function.End.applyMulAction` is faithful. -/
instance apply_FaithfulSMul : FaithfulSMul (Function.End α) α where eq_of_smul_eq_smul := funext

end Function.End

/-! #### Tautological action by `Equiv.Perm` -/

namespace Equiv.Perm

/-- The tautological action by `Equiv.Perm α` on `α`.

This generalizes `Function.End.applyMulAction`. -/
instance applyMulAction (α : Type*) : MulAction (Perm α) α where
  smul f a := f a
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[simp]
protected lemma smul_def {α : Type*} (f : Perm α) (a : α) : f • a = f a := rfl

/-- `Equiv.Perm.applyMulAction` is faithful. -/
instance applyFaithfulSMul (α : Type*) : FaithfulSMul (Perm α) α := ⟨Equiv.ext⟩

end Equiv.Perm

/-! #### Tautological action by `MulAut` -/

namespace MulAut
variable [Monoid M]

/-- The tautological action by `MulAut M` on `M`. -/
instance applyMulAction : MulAction (MulAut M) M where
  smul := (· <| ·)
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/-- The tautological action by `MulAut M` on `M`.

This generalizes `Function.End.applyMulAction`. -/
instance applyMulDistribMulAction : MulDistribMulAction (MulAut M) M where
  smul := (· <| ·)
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_one := map_one
  smul_mul := map_mul

@[simp] protected lemma smul_def (f : MulAut M) (a : M) : f • a = f a := rfl

/-- `MulAut.applyDistribMulAction` is faithful. -/
instance apply_faithfulSMul : FaithfulSMul (MulAut M) M where eq_of_smul_eq_smul := MulEquiv.ext

end MulAut

/-! #### Tautological action by `AddAut` -/

namespace AddAut
variable [AddMonoid M]

/-- The tautological action by `AddAut M` on `M`. -/
instance applyMulAction : MulAction (AddAut M) M where
  smul := (· <| ·)
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[simp] protected lemma smul_def (f : AddAut M) (a : M) : f • a = f a := rfl

/-- `AddAut.applyDistribMulAction` is faithful. -/
instance apply_faithfulSMul : FaithfulSMul (AddAut M) M where eq_of_smul_eq_smul := AddEquiv.ext

end AddAut

/-! ### Converting actions to and from homs to the monoid/group of endomorphisms/automorphisms -/

section Monoid
variable [Monoid M]

/-- The monoid hom representing a monoid action.

When `M` is a group, see `MulAction.toPermHom`. -/
def MulAction.toEndHom [MulAction M α] : M →* Function.End α where
  toFun := (· • ·)
  map_one' := funext (one_smul M)
  map_mul' x y := funext (mul_smul x y)

/-- The monoid action induced by a monoid hom to `Function.End α`

See note [reducible non-instances]. -/
abbrev MulAction.ofEndHom (f : M →* Function.End α) : MulAction M α := .compHom α f

end Monoid

section AddMonoid
variable [AddMonoid M]

/-- The additive monoid hom representing an additive monoid action.

When `M` is a group, see `AddAction.toPermHom`. -/
def AddAction.toEndHom [AddAction M α] : M →+ Additive (Function.End α) :=
  MonoidHom.toAdditive'' MulAction.toEndHom

/-- The additive action induced by a hom to `Additive (Function.End α)`

See note [reducible non-instances]. -/
abbrev AddAction.ofEndHom (f : M →+ Additive (Function.End α)) : AddAction M α := .compHom α f

end AddMonoid

section Group
variable (G α) [Group G] [MulAction G α]

/-- Given an action of a group `G` on a set `α`, each `g : G` defines a permutation of `α`. -/
@[simps]
def MulAction.toPermHom : G →* Equiv.Perm α where
  toFun := MulAction.toPerm
  map_one' := Equiv.ext <| one_smul G
  map_mul' u₁ u₂ := Equiv.ext <| mul_smul (u₁ : G) u₂

end Group

section AddGroup
variable (G α) [AddGroup G] [AddAction G α]

/-- Given an action of an additive group `G` on a set `α`, each `g : G` defines a permutation of
`α`. -/
@[simps!]
def AddAction.toPermHom : G →+ Additive (Equiv.Perm α) :=
  MonoidHom.toAdditive'' <| MulAction.toPermHom ..

end AddGroup

section MulDistribMulAction
variable (M) [Group G] [Monoid M] [MulDistribMulAction G M]

/-- Each element of the group defines a multiplicative monoid isomorphism.

This is a stronger version of `MulAction.toPerm`. -/
@[simps +simpRhs]
def MulDistribMulAction.toMulEquiv (x : G) : M ≃* M :=
  { MulDistribMulAction.toMonoidHom M x, MulAction.toPermHom G M x with }

variable (G) in
/-- Each element of the group defines a multiplicative monoid isomorphism.

This is a stronger version of `MulAction.toPermHom`. -/
@[simps]
def MulDistribMulAction.toMulAut : G →* MulAut M where
  toFun := MulDistribMulAction.toMulEquiv M
  map_one' := MulEquiv.ext (one_smul _)
  map_mul' _ _ := MulEquiv.ext (mul_smul _ _)

end MulDistribMulAction

section Arrow
variable [Group G] [MulAction G A] [Monoid M]

attribute [local instance] arrowMulDistribMulAction

/-- Given groups `G H` with `G` acting on `A`, `G` acts by
multiplicative automorphisms on `A → H`. -/
@[simps!] def mulAutArrow : G →* MulAut (A → M) := MulDistribMulAction.toMulAut _ _

end Arrow
