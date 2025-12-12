/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Action.Basic
public import Mathlib.Algebra.Group.Action.Hom
public import Mathlib.Algebra.Group.End

/-!
# Interaction between actions and endomorphisms/automorphisms

This file provides two things:
* The tautological actions by endomorphisms/automorphisms on their base type.
* An action by a monoid/group on a type is the same as a hom from the monoid/group to
  endomorphisms/automorphisms of the type.

## Tags

monoid action, group action
-/

@[expose] public section

assert_not_exists MonoidWithZero

open Function (Injective Surjective)

variable {G M N A α : Type*}

/-! ### Tautological actions -/

/-! #### Tautological action by `Function.End` -/

namespace Function.End

/-- The tautological action by `Function.End α` on `α`.

This is generalized to bundled endomorphisms by:
* `Equiv.Perm.applyMonoidAction`
* `AddMonoid.End.applyDistribMulAction`
* `AddMonoid.End.applyModule`
* `AddAut.applyDistribMulAction`
* `MulAut.applyMulDistribMulAction`
* `LinearEquiv.applyDistribMulAction`
* `LinearMap.applyModule`
* `RingHom.applyMulSemiringAction`
* `RingAut.applyMulSemiringAction`
* `AlgEquiv.applyMulSemiringAction`
* `RelHom.applyMonoidAction`
* `RelEmbedding.applyMonoidAction`
* `RelIso.applyMonoidAction`
-/
instance applyMonoidAction : MonoidAction (Function.End α) α where
  smul := (· <| ·)
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/-- The tautological additive action by `Additive (Function.End α)` on `α`. -/
instance applyAddMonoidAction : AddMonoidAction (Additive (Function.End α)) α := inferInstance

@[simp] lemma smul_def (f : Function.End α) (a : α) : f • a = f a := rfl

--TODO - This statement should be somethting like `toFun (f * g) = toFun f ∘ toFun g`
lemma mul_def (f g : Function.End α) : (f * g) = f ∘ g := rfl

--TODO - This statement should be somethting like `toFun 1 = id`
lemma one_def : (1 : Function.End α) = id := rfl

/-- `Function.End.applyMonoidAction` is faithful. -/
instance apply_FaithfulSMul : FaithfulSMul (Function.End α) α where eq_of_smul_eq_smul := funext

end Function.End

/-! #### Tautological action by `Equiv.Perm` -/

namespace Equiv.Perm

/-- The tautological action by `Equiv.Perm α` on `α`.

This generalizes `Function.End.applyMonoidAction`. -/
instance applyMonoidAction (α : Type*) : MonoidAction (Perm α) α where
  smul f a := f a
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[simp]
protected lemma smul_def {α : Type*} (f : Perm α) (a : α) : f • a = f a := rfl

/-- `Equiv.Perm.applyMonoidAction` is faithful. -/
instance applyFaithfulSMul (α : Type*) : FaithfulSMul (Perm α) α := ⟨Equiv.ext⟩

/-- The permutation group of `α` acts transitively on `α`. -/
instance : MonoidAction.IsPretransitive (Perm α) α := by
  rw [MonoidAction.isPretransitive_iff]
  classical
  intro x y
  use Equiv.swap x y
  simp

end Equiv.Perm

/-! #### Tautological action by `MulAut` -/

namespace MulAut
variable [Monoid M]

/-- The tautological action by `MulAut M` on `M`. -/
instance applyMonoidAction : MonoidAction (MulAut M) M where
  smul := (· <| ·)
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/-- The tautological action by `MulAut M` on `M`.

This generalizes `Function.End.applyMonoidAction`. -/
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
instance applyMonoidAction : MonoidAction (AddAut M) M where
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

When `M` is a group, see `MonoidAction.toPermHom`. -/
def MonoidAction.toEndHom [MonoidAction M α] : M →* Function.End α where
  toFun := (· • ·)
  map_one' := funext (one_smul M)
  map_mul' x y := funext (mul_smul x y)

/-- The monoid action induced by a monoid hom to `Function.End α`

See note [reducible non-instances]. -/
abbrev MonoidAction.ofEndHom (f : M →* Function.End α) : MonoidAction M α := .compHom α f

end Monoid

section AddMonoid
variable [AddMonoid M]

/-- The additive monoid hom representing an additive monoid action.

When `M` is a group, see `AddMonoidAction.toPermHom`. -/
def AddMonoidAction.toEndHom [AddMonoidAction M α] : M →+ Additive (Function.End α) :=
  MonoidAction.toEndHom.toAdditiveRight

/-- The additive action induced by a hom to `Additive (Function.End α)`

See note [reducible non-instances]. -/
abbrev AddMonoidAction.ofEndHom (f : M →+ Additive (Function.End α)) :
    AddMonoidAction M α := .compHom α f

end AddMonoid

section Group
variable (G α) [Group G] [MonoidAction G α]

/-- Given an action of a group `G` on a set `α`, each `g : G` defines a permutation of `α`. -/
@[simps]
def MonoidAction.toPermHom : G →* Equiv.Perm α where
  toFun := MonoidAction.toPerm
  map_one' := Equiv.ext <| one_smul G
  map_mul' u₁ u₂ := Equiv.ext <| mul_smul (u₁ : G) u₂

lemma MonoidAction.coe_toPermHom :
    ⇑(MonoidAction.toPermHom G α) = MonoidAction.toPerm :=
  rfl

lemma MonoidAction.toPerm_one :
    (MonoidAction.toPerm (1 : G))  = (1 : Equiv.Perm α) := by
  aesop

end Group

section AddGroup
variable (G α) [AddGroup G] [AddMonoidAction G α]

/-- Given an action of an additive group `G` on a set `α`, each `g : G` defines a permutation of
`α`. -/
@[simps!]
def AddMonoidAction.toPermHom : G →+ Additive (Equiv.Perm α) :=
  (MonoidAction.toPermHom ..).toAdditiveRight

lemma AddMonoidAction.coe_toPermHom :
    ⇑(AddMonoidAction.toPermHom G α) = AddMonoidAction.toPerm :=
  rfl

theorem AddMonoidAction.toPerm_zero :
    (AddMonoidAction.toPerm (0 : G))  = (1 : Equiv.Perm α) := by
  aesop

end AddGroup

section MulDistribMulAction
variable (M) [Group G] [Monoid M] [MulDistribMulAction G M]

/-- Each element of the group defines a multiplicative monoid isomorphism.

This is a stronger version of `MonoidAction.toPerm`. -/
@[simps +simpRhs]
def MulDistribMulAction.toMulEquiv (x : G) : M ≃* M :=
  { MulDistribMulAction.toMonoidHom M x, MonoidAction.toPermHom G M x with }

variable (G) in
/-- Each element of the group defines a multiplicative monoid isomorphism.

This is a stronger version of `MonoidAction.toPermHom`. -/
@[simps]
def MulDistribMulAction.toMulAut : G →* MulAut M where
  toFun := MulDistribMulAction.toMulEquiv M
  map_one' := MulEquiv.ext (one_smul _)
  map_mul' _ _ := MulEquiv.ext (mul_smul _ _)

end MulDistribMulAction

section Arrow
variable [Group G] [MonoidAction G A] [Monoid M]

attribute [local instance] arrowMulDistribMulAction

/-- Given groups `G H` with `G` acting on `A`, `G` acts by
multiplicative automorphisms on `A → H`. -/
@[simps!] def mulAutArrow : G →* MulAut (A → M) := MulDistribMulAction.toMulAut _ _

end Arrow
