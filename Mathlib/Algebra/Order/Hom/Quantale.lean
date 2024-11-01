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

This file defines the bundled structures for quantale homomorphisms and unital quantale
homomorphism. Namely, we define `QuantaleHom` (resp., `AddQuantaleHom`) to be bundled
homomorphisms between multiplicative (resp.,additive) quantales and `OneQuantaleHom`
(resp. `ZeroAddQuantaleHom`) to be bundled homomorphisms between multiplicative (resp. additive)
unital quantales. Similar, we define `QuantaleIso`, `AddQuantaleIso`, `OneQuantaleIso`,
and `ZeroQuantaleIso` to be bundled isomorphisms between multiplicative (resp. additive)
(unital) quantales.

We also define coercion to a function, and usual operations: composition, identity homomorphism,
pointwise multiplication and pointwise inversion.

## Typeclasses

* `QuantaleHom`, resp. `AddQuantaleHom`: (Additive) Quantale homomorphisms are semigroup
homomorphisms as well as complete lattice homomorphisms
* `QuantaleHomClass`, resp. `AddQuantaleHomClass`: typeclass of (additive) quantale homomorphisms
* `OneQuantaleHom`, resp. `ZeroAddQuantaleHom`: (Additive) unital quantale homomorphisms are
monoid homomorphisms as well as complete lattice homomorphisms
* `OneQuantaleHomClass`, resp. `ZeroAddQuantaleHomClass`: typeclass of (additive) unital quantale
homomorphisms
* `QuantaleIso`, resp. `AddQuantaleIso`: (Additive) Quantale isomorphisms.
* `QuantaleIsoClass`, resp. `AddQuantaleIsoClass`: typeclass of (additive) quantale isomorphisms
* `OneQuantaleIso`, resp. `ZeroAddQuantaleIso`: (Additive) unital quantale isomorphisms.
* `OneQuantaleIsoClass`, resp. `ZeroAddQuantaleIsoClass`: typeclass of (additive) unital quantale
isomorphisms

## Notation

* `→+q`: Bundled additive quantale homs.
* `→*q`: Bundled multiplicative quantale homs.
* `→+₀q`: Bundled additive unital quantale homs.
* `→*₁q`: Bundled multiplicative unital quantale homs.
* `≃+o`: Bundled additive quantale isos.
* `≃*o`: Bundled quantale isos.
* `≃+₀o`: Bundled additive unital quantale isos.
* `≃*₁o`: Bundled unital quantale isos.
-/

/- Additive Quantale Homomorphisms-/

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

/- Quantale Homomorphisms-/

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

/- Additive Unital Quantale Homomorphisms-/

namespace AddQuantale

/-- `M →+₀q N` is the type of functions `M → N` that preserve the `AddQuantale` structure
over a monoid rather than a semigroup.

When possible, instead of parametrizing results over `(f : M →+₀q N)`,
you should parametrize over `(F : Type*) [ZeroAddQuantaleHomClass F M N] (f : F)`.

When you extend this structure, make sure to extend `ZeroAddQuantaleHomClass`.
-/
structure ZeroAddQuantaleHom (M N : Type*)
  [AddMonoid M] [AddMonoid N] [AddQuantale M] [AddQuantale N]
  extends AddMonoidHom M N, CompleteLatticeHom M N

attribute [nolint docBlame] AddQuantaleHom.toAddHom
attribute [nolint docBlame] AddQuantaleHom.toCompleteLatticeHom

/-- `M →+₀q N` denotes the type of additive unital quantale homomorphisms from `M` to `N`. -/
infixr:25 " →+₀q " => ZeroAddQuantaleHom

/-- `ZeroAddQuantaleHomClass F M N` states that `F` is a type of `ZeroAddQuantale`-preserving
homomorphisms.

You should also extend this typeclass when you extend `ZeroAddQuantaleHom`.
-/
class ZeroAddQuantaleHomClass (F : Type*) (M N : outParam Type*)
    [AddMonoid M] [AddMonoid N] [AddQuantale M] [AddQuantale N] [FunLike F M N]
    extends AddMonoidHomClass F M N, CompleteLatticeHomClass F M N : Prop

-- Instances and lemmas are defined below through `@[to_additive]`.

end AddQuantale

/- Unital Quantale Homomorphisms-/

namespace Quantale

/-- `M →*₁q N` is the type of functions `M → N` that preserve the `Quantale` structure over a
monoid rather than a semigroup.

When possible, instead of parametrizing results over `(f : M →+₁q N)`,
you should parametrize over `(F : Type*) [OneQuantaleHomClass F M N] (f : F)`.

When you extend this structure, make sure to extend `OneQuantaleHomClass`.
-/
@[to_additive]
structure OneQuantaleHom (M N : Type*)
  [Monoid M] [Monoid N] [Quantale M] [Quantale N]
  extends MonoidHom M N, CompleteLatticeHom M N

attribute [nolint docBlame] QuantaleHom.toMulHom
attribute [nolint docBlame] QuantaleHom.toCompleteLatticeHom

/-- `M →*₁q N` denotes the type of additive quantale homomorphisms from `M` to `N`. -/
infixr:25 " →*₁q " => OneQuantaleHom

/-- `OneQuantaleHomClass F M N` states that `F` is a type of `OneQuantale`-preserving
homomorphisms.

You should also extend this typeclass when you extend `OneQuantaleHom`.
-/
@[to_additive]
class OneQuantaleHomClass (F : Type*) (M N : outParam Type*)
    [Monoid M] [Monoid N] [Quantale M] [Quantale N] [FunLike F M N]
    extends MonoidHomClass F M N, CompleteLatticeHomClass F M N : Prop

variable {M N : Type*} {F : Type*}
variable [Monoid M] [Monoid N] [Quantale M] [Quantale N] [FunLike F M N]

@[to_additive]
instance OneQuantaleHom.instFunLike : FunLike (M →*₁q N) M N where
  coe f := f.toFun
  coe_injective' f g h := by
    cases f
    cases g
    congr
    apply DFunLike.coe_injective'
    exact h

@[to_additive]
instance OneQuantaleHom.instOneQuantaleHomClass : OneQuantaleHomClass (M →*₁q N) M N where
  map_mul f := f.toMonoidHom.map_mul'
  map_sInf f := f.toCompleteLatticeHom.map_sInf'
  map_sSup f := f.toCompleteLatticeHom.map_sSup'
  map_one f := f.toMonoidHom.map_one'

/-- Turn an element of a type `F` satisfying `OneQuantaleHomClass F M N` into an actual
`OneQuantaleHom`. This is declared as the default coercion from `F` to `M →*₁q N`. -/
@[to_additive (attr := coe)
"Turn an element of a type `F` satisfying `ZeroAddQuantaleHomClass F M N` into an
actual `ZeroAddQuantaleHom`. This is declared as the default coercion from `F` to `M →+₀q N`."]
def OneQuantaleHomClass.toOneQuantaleHom [OneQuantaleHomClass F M N] (f : F) : M →*₁q N :=
  { (f : MonoidHom M N), (f : CompleteLatticeHom M N) with }

/-- Any type satisfying `OneQuantaleHomClass` can be cast into `OneQuantaleHom` via
`OneQuantaleHomClass.toOneQuantaleHom`. -/
@[to_additive "Any type satisfying `ZeroAddQuantaleHomClass` can be cast into `ZeroAddQuantaleHom`
via `ZeroAddQuantaleHomClass.toZeroAddQuantaleHom`."]
instance [OneQuantaleHomClass F M N] : CoeTC F (M →*₁q N) :=
  ⟨OneQuantaleHomClass.toOneQuantaleHom⟩

@[to_additive (attr := simp)]
theorem OneQuantaleHom.coe_coe [OneQuantaleHomClass F M N] (f : F) :
   ((f : M →*₁q N) : M → N) = f := rfl

end Quantale
