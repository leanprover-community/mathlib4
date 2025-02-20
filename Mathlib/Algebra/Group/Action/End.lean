/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Yury Kudryashov
-/
import Mathlib.Algebra.Group.Action.Faithful
import Mathlib.Algebra.Group.Action.Hom
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.TypeTags.Hom
import Mathlib.Logic.Embedding.Basic

/-!
# Endomorphisms, homomorphisms and group actions

This file defines `Function.End` as the monoid of endomorphisms on a type,
and provides results relating group actions with these endomorphisms.

## Notation

- `a • b` is used as notation for `SMul.smul a b`.
- `a +ᵥ b` is used as notation for `VAdd.vadd a b`.

## Implementation details

This file should avoid depending on other parts of `GroupTheory`, to avoid import cycles.
More sophisticated lemmas belong in `GroupTheory.GroupAction`.

## Tags

group action
-/

assert_not_exists MonoidWithZero

open Function (Injective Surjective)

variable {M N α : Type*}

namespace MulAction
variable [Monoid M] [MulAction M α]

variable (M α) in
/-- Embedding of `α` into functions `M → α` induced by a multiplicative action of `M` on `α`. -/
@[to_additive
"Embedding of `α` into functions `M → α` induced by an additive action of `M` on `α`."]
def toFun : α ↪ M → α :=
  ⟨fun y x ↦ x • y, fun y₁ y₂ H ↦ one_smul M y₁ ▸ one_smul M y₂ ▸ by convert congr_fun H 1⟩

@[to_additive (attr := simp)]
lemma toFun_apply (x : M) (y : α) : MulAction.toFun M α y x = x • y := rfl

end MulAction

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
-/
instance Function.End.applyMulAction : MulAction (Function.End α) α where
  smul := (· <| ·)
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/-- The tautological additive action by `Additive (Function.End α)` on `α`. -/
instance Function.End.applyAddAction : AddAction (Additive (Function.End α)) α := inferInstance

@[simp] lemma Function.End.smul_def (f : Function.End α) (a : α) : f • a = f a := rfl

--TODO - This statement should be somethting like `toFun (f * g) = toFun f ∘ toFun g`
lemma Function.End.mul_def (f g : Function.End α) : (f * g) = f ∘ g := rfl

--TODO - This statement should be somethting like `toFun 1 = id`
lemma Function.End.one_def : (1 : Function.End α) = id := rfl

/-- `Function.End.applyMulAction` is faithful. -/
instance Function.End.apply_FaithfulSMul : FaithfulSMul (Function.End α) α where
  eq_of_smul_eq_smul := funext

/-- The monoid hom representing a monoid action.

When `M` is a group, see `MulAction.toPermHom`. -/
def MulAction.toEndHom [Monoid M] [MulAction M α] : M →* Function.End α where
  toFun := (· • ·)
  map_one' := funext (one_smul M)
  map_mul' x y := funext (mul_smul x y)

/-- The additive monoid hom representing an additive monoid action.

When `M` is a group, see `AddAction.toPermHom`. -/
def AddAction.toEndHom [AddMonoid M] [AddAction M α] : M →+ Additive (Function.End α) :=
  MonoidHom.toAdditive'' MulAction.toEndHom

/-- The monoid action induced by a monoid hom to `Function.End α`

See note [reducible non-instances]. -/
abbrev MulAction.ofEndHom [Monoid M] (f : M →* Function.End α) : MulAction M α := .compHom α f

/-- The additive action induced by a hom to `Additive (Function.End α)`

See note [reducible non-instances]. -/
abbrev AddAction.ofEndHom [AddMonoid M] (f : M →+ Additive (Function.End α)) : AddAction M α :=
  .compHom α f

namespace MulAut
variable [Monoid M]

/-- The tautological action by `MulAut M` on `M`. -/
instance applyMulAction : MulAction (MulAut M) M where
  smul := (· <| ·)
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[simp] protected lemma smul_def (f : MulAut M) (a : M) : f • a = f a := rfl

/-- `MulAut.applyDistribMulAction` is faithful. -/
instance apply_faithfulSMul : FaithfulSMul (MulAut M) M where eq_of_smul_eq_smul := MulEquiv.ext

end MulAut

namespace AddAut

variable (A) [Add A]

/-- The tautological action by `AddAut A` on `A`. -/
instance applyMulAction {A} [AddMonoid A] : MulAction (AddAut A) A where
  smul := (· <| ·)
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[simp] protected lemma smul_def {A} [AddMonoid A] (f : AddAut A) (a : A) : f • a = f a := rfl

/-- `AddAut.applyDistribMulAction` is faithful. -/
instance apply_faithfulSMul {A} [AddMonoid A] : FaithfulSMul (AddAut A) A where
  eq_of_smul_eq_smul := AddEquiv.ext

end AddAut
