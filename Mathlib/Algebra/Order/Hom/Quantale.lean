/-
Copyright (c) 2024 Pieter Cuijpers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pieter Cuijpers
-/
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Order.Hom.Monoid
import Mathlib.Algebra.Order.Quantale
import Mathlib.Data.FunLike.Basic
import Mathlib.Order.Hom.CompleteLattice

/-!
# Quantale homomorphism classes

This file defines the bundled structures for (unital) quantale homomorphisms and unital quantale
homomorphism. Namely, we define `QuantaleHom` (resp., `AddQuantaleHom`) to be bundled
homomorphisms between multiplicative (resp.,additive) quantales and `OneQuantaleHom`
(resp. `ZeroAddQuantaleHom`) to be bundled homomorphisms between multiplicative (resp. additive)
unital quantales.

We also define coercion to a function, and usual operations: composition, identity homomorphism,
pointwise multiplication and pointwise inversion.

We finally include the theorem that every ordered (additive) monoid iso is a (additive) unital
quantale iso.

## Typeclasses

* `QuantaleHom`, resp. `AddQuantaleHom`: (Additive) Quantale homomorphisms are semigroup
homomorphisms as well as complete lattice homomorphisms
* `OneQuantaleHom`, resp. `ZeroAddQuantaleHom`: (Additive) unital quantale homomorphisms are
monoid homomorphisms as well as complete lattice homomorphisms

In the file Mathlib.Algebra.Order.Hom.Monoid it is mentioned that there used to be classes:
`OrderAddMonoidHomClass` etc., but that in #10544 we migrated from these typeclasses to
assumptions like `[FunLike F M N] [MonoidHomClass F M N] [OrderHomClass F M N]`,
making some definitions and lemmas irrelevant. This suggests that for quantales we also only
need to define `AddQuantaleHom` but do not need `AddQuantaleHomClass`.

## Notation

We only introduce notations for the homomorhpisms on unital quantales, since the notation
`→*` in Mathlib already refers to monoids homomorphisms, rather than semigroup homomorphisms.
Also, the assumption that a quantale is unital is more common than the assumption that it is not.

* `→+q`: Bundled additive unital quantale homs.
* `→*q`: Bundled multiplicative unital quantale homs.

## TODO

The part where we define the usual operations: composition, identity homomorphism, pointwise
multiplication and pointwise inversion, still needs to be added

-/

/- Additive Quantale Homomorphisms-/

namespace AddQuantale

/-- `AddQuantaleHom` is the type of functions `M → N` that preserve the `AddQuantale` structure.

When possible, instead of parametrizing results over `(f : AddQuantaleHom M N)`, you should
parametrize over
`(F : Type*) [FunLike F M N] [AddHomClass F M N] [CompleteLatticeHomClass F M N] (f : F)`.
-/
structure AddQuantaleHom (M N : Type*)
  [AddSemigroup M] [AddSemigroup N] [AddQuantale M] [AddQuantale N]
  extends AddHom M N, CompleteLatticeHom M N

attribute [nolint docBlame] AddQuantaleHom.toAddHom
attribute [nolint docBlame] AddQuantaleHom.toCompleteLatticeHom

-- Instances and lemmas are defined below through `@[to_additive]`.

end AddQuantale

/- Quantale Homomorphisms-/

namespace Quantale

/-- `QuantaleHom` is the type of functions `M → N` that preserve the `Quantale` structure.

When possible, instead of parametrizing results over `(f : QuantaleHom M N)`, you should
parametrize over
`(F : Type*) [FunLike F M N] [MulHomClass F M N] [CompleteLatticeHomClass F M N] (f : F)`.
-/
@[to_additive]
structure QuantaleHom (M N : Type*)
  [Semigroup M] [Semigroup N] [Quantale M] [Quantale N]
  extends MulHom M N, CompleteLatticeHom M N

attribute [nolint docBlame] QuantaleHom.toMulHom
attribute [nolint docBlame] QuantaleHom.toCompleteLatticeHom

variable {M N : Type*} {F : Type*}
variable [Semigroup M] [Semigroup N] [Quantale M] [Quantale N] [FunLike F M N]

@[to_additive]
instance QuantaleHom.instFunLike : FunLike (QuantaleHom M N) M N where
  coe f := f.toFun
  coe_injective' f g h := by
    cases f
    cases g
    congr
    apply DFunLike.coe_injective'
    exact h

/-- Turn a `Funlike F` satisfying `[MulHomClass F M N] [CompleteLatticeHomClass F M N]` into
a `QuantaleHom`. This is declared as the default coercion from `F` to `M →*q N`. -/
@[to_additive (attr := coe)
"Turn a `Funlike F` satisfying `[AddHomClass F M N] [CompleteLatticeHomClass F M N]` into
an `AddQuantaleHom`. This is declared as the default coercion from `F` to `M →*q N`."]
def instQuantaleHom
  [FunLike F M N] [MulHomClass F M N] [CompleteLatticeHomClass F M N] (f : F) : QuantaleHom M N :=
  { (f : MulHom M N), (f : CompleteLatticeHom M N) with }

@[to_additive]
instance
  [FunLike F M N] [MulHomClass F M N] [CompleteLatticeHomClass F M N] :
  CoeTC F (QuantaleHom M N) := ⟨instQuantaleHom⟩

@[to_additive (attr := simp)]
theorem QuantaleHom.coe_coe
 [MulHomClass F M N] [CompleteLatticeHomClass F M N] (f : F) :
 ((f : QuantaleHom M N) : M → N) = f := rfl

end Quantale

/- Additive Unital Quantale Homomorphisms-/

namespace AddQuantale

/-- `M →+q N` is the type of functions `M → N` that preserve the `AddQuantale` structure
over a monoid rather than a semigroup.

When possible, instead of parametrizing results over `(f : M →+q N)`,
you should parametrize over
`(F : Type*) [FunLike F M N] [AddMonoidHomClass F M N] [CompleteLatticeHomClass F M N] (f : F)`.
-/
structure ZeroAddQuantaleHom (M N : Type*)
  [AddMonoid M] [AddMonoid N] [AddQuantale M] [AddQuantale N]
  extends AddMonoidHom M N, AddQuantaleHom M N

attribute [nolint docBlame] ZeroAddQuantaleHom.toAddMonoidHom
attribute [nolint docBlame] ZeroAddQuantaleHom.toAddQuantaleHom

/-- `M →+q N` denotes the type of additive unital quantale homomorphisms from `M` to `N`. -/
infixr:25 " →+q " => ZeroAddQuantaleHom

end AddQuantale

/- Unital Quantale Homomorphisms-/

namespace Quantale

/-- `M →*q N` is the type of functions `M → N` that preserve the `Quantale` structure over a
monoid rather than a semigroup.

When possible, instead of parametrizing results over `(f : M →*q N)`,
you should parametrize over
`(F : Type*) [FunLike F M N] [MonoidHomClass F M N] [CompleteLatticeHomClass F M N] (f : F)`.
-/
@[to_additive]
structure OneQuantaleHom (M N : Type*)
  [Monoid M] [Monoid N] [Quantale M] [Quantale N]
  extends MonoidHom M N, QuantaleHom M N

attribute [nolint docBlame] OneQuantaleHom.toMonoidHom
attribute [nolint docBlame] OneQuantaleHom.toQuantaleHom

/-- `M →*q N` denotes the type of additive quantale homomorphisms from `M` to `N`. -/
infixr:25 " →*q " => OneQuantaleHom

variable {M N : Type*} {F : Type*}
variable [Monoid M] [Monoid N] [Quantale M] [Quantale N] [FunLike F M N]

@[to_additive]
instance OneQuantaleHom.instFunLike : FunLike (M →*q N) M N where
  coe f := f.toFun
  coe_injective' f g h := by
    cases f
    cases g
    congr
    apply DFunLike.coe_injective'
    exact h

/-- Turn a `Funlike F` satisfying `MonoidHomClass` and `CompleteLatticeHomClass`
into a `OneQuantaleHom`. This is declared as the default coercion from `F` to `M →*q N`. -/
@[to_additive (attr := coe)
"Turn a `Funlike F` satisfying `AddMonoidHomClass` and `CompleteLatticeHomClass` into a
`ZeroAddQuantaleHom`. This is declared as the default coercion from `F` to `M →+q N`."]
def instOneQuantaleHom
  [FunLike F M N] [MonoidHomClass F M N] [CompleteLatticeHomClass F M N] (f : F) : M →*q N :=
  { (f : MonoidHom M N), (f : CompleteLatticeHom M N) with }

@[to_additive]
instance [FunLike F M N] [MonoidHomClass F M N] [CompleteLatticeHomClass F M N] :
  CoeTC F (M →*q N) := ⟨instOneQuantaleHom⟩

@[to_additive (attr := simp)]
theorem OneQuantaleHom.coe_coe
  [MonoidHomClass F M N] [CompleteLatticeHomClass F M N] (f : F) :
  ((f : M →*q N) : M → N) = f := rfl

/- Isomorphisms -/

example (f : M ≃*o N) : M →*q N := instOneQuantaleHom f

end Quantale
