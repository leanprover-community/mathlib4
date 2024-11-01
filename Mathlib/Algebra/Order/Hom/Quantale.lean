/-
Copyright (c) 2024 Pieter Cuijpers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pieter Cuijpers
-/
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Order.Hom.Basic
import Mathlib.Algebra.Order.Hom.Monoid
import Mathlib.Algebra.Order.Quantale
import Mathlib.Data.FunLike.Basic
import Mathlib.Order.Hom.CompleteLattice

/-!
# Quantale homomorphism classes

This file defines the bundled structures for quantale homomorphisms. Namely, we define
`QuantaleHom` (resp., `AddQuantaleHom`) to be bundled homomorphisms between multiplicative (resp.,
additive) quantales.

We also define coercion to a function, and usual operations: composition, identity homomorphism,
pointwise multiplication and pointwise inversion.

## Typeclasses

* `QuantaleHom`, resp. `AddQuantaleHom`: (Additive) Quantale homomorphisms are semigroup
homomorphisms as well as complete lattice homomorphisms
* `QuantaleHomClass`, resp. `AddQuantaleHomClass`: typeclass of (additive) quantale homomorphisms

## Todo

* Add lax and oplax (i.e. supadditive and superadditive) variants of quantale homomorphisms

-/

namespace AddQuantale

/-- `M →+q N` is the type of functions `M → N` that preserve the `AddQuantale` structure.

When possible, instead of parametrizing results over `(f : M →+q N)`,
you should parametrize over `(F : Type*) [AddQuantaleHomClass F M N] (f : F)`.

When you extend this structure, make sure to extend `AddQuantaleHomClass`.
-/
structure AddQuantaleHom (M N : Type*)
  [AddSemigroup M] [AddSemigroup N] [AddQuantale M] [AddQuantale N]
  extends AddHom M N, CompleteLatticeHom M N

attribute [nolint docBlame] AddQuantaleHom.toAddHom
attribute [nolint docBlame] AddQuantaleHom.toCompleteLatticeHom

/-- `M →+q N` denotes the type of additive quantale homomorphisms from `M` to `N`. -/
infixr:25 " →+q " => AddQuantaleHom

/-- `AddQuantaleHomClass F M N` states that `F` is a type of `AddQuantale`-preserving
homomorphisms.

You should also extend this typeclass when you extend `AddQuantaleHom`.
-/
class AddQuantaleHomClass (F : Type*) (M N : outParam Type*)
    [AddSemigroup M] [AddSemigroup N] [AddQuantale M] [AddQuantale N] [FunLike F M N]
    extends AddHomClass F M N, CompleteLatticeHomClass F M N : Prop

-- Instances and lemmas are defined below through `@[to_additive]`.

end AddQuantale

namespace Quantale

/-- `M →*q N` is the type of functions `M → N` that preserve the `Quantale` structure.

When possible, instead of parametrizing results over `(f : M →+q N)`,
you should parametrize over `(F : Type*) [QuantaleHomClass F M N] (f : F)`.

When you extend this structure, make sure to extend `QuantaleHomClass`.
-/
@[to_additive]
structure QuantaleHom (M N : Type*)
  [Semigroup M] [Semigroup N] [Quantale M] [Quantale N]
  extends MulHom M N, CompleteLatticeHom M N

attribute [nolint docBlame] QuantaleHom.toMulHom
attribute [nolint docBlame] QuantaleHom.toCompleteLatticeHom

/-- `M →*q N` denotes the type of additive quantale homomorphisms from `M` to `N`. -/
infixr:25 " →*q " => QuantaleHom

/-- `QuantaleHomClass F M N` states that `F` is a type of `Quantale`-preserving
homomorphisms.

You should also extend this typeclass when you extend `QuantaleHom`.
-/
@[to_additive]
class QuantaleHomClass (F : Type*) (M N : outParam Type*)
    [Semigroup M] [Semigroup N] [Quantale M] [Quantale N] [FunLike F M N]
    extends MulHomClass F M N, CompleteLatticeHomClass F M N : Prop

variable {M N : Type*} {F : Type*}
variable [Semigroup M] [Semigroup N] [Quantale M] [Quantale N] [FunLike F M N]

@[to_additive]
instance QuantaleHom.instFunLike : FunLike (M →*q N) M N where
  coe f := f.toFun
  coe_injective' f g h := by
    cases f
    cases g
    congr
    apply DFunLike.coe_injective'
    exact h

@[to_additive]
instance QuantaleHom.instQuantaleHomClass : QuantaleHomClass (M →*q N) M N where
  map_mul f := f.toMulHom.map_mul'
  map_sInf f := f.toCompleteLatticeHom.map_sInf'
  map_sSup f := f.toCompleteLatticeHom.map_sSup'

/-- Turn an element of a type `F` satisfying `QuantaleHomClass F M N` into an actual
`QuantaleHom`. This is declared as the default coercion from `F` to `M →*q N`. -/
@[to_additive (attr := coe)
"Turn an element of a type `F` satisfying `AddQuantaleHomClass F M N` into an
actual `AddQuantaleHom`. This is declared as the default coercion from `F` to `M →+q N`."]
def QuantaleHomClass.toQuantaleHom [QuantaleHomClass F M N] (f : F) : M →*q N :=
  { (f : MulHom M N), (f : CompleteLatticeHom M N) with }

/-- Any type satisfying `QuantaleHomClass` can be cast into `QuantaleHom` via
`QuantaleHomClass.toQuantaleHom`. -/
@[to_additive "Any type satisfying `AddQuantaleHomClass` can be cast into `AddQuantaleHom` via
`AddQuantaleHomClass.toAddQuantaleHom`."]
instance [QuantaleHomClass F M N] : CoeTC F (M →*q N) :=
  ⟨QuantaleHomClass.toQuantaleHom⟩

@[to_additive (attr := simp)]
theorem QuantaleHom.coe_coe [QuantaleHomClass F M N] (f : F) : ((f : M →*q N) : M → N) = f := rfl

end Quantale
