/-
Copyright (c) 2024 Pieter Cuijpers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pieter Cuijpers
-/
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Order.Hom.Monoid
import Mathlib.Algebra.Order.Quantale
import Mathlib.Order.Hom.CompleteLattice

/-!
# Quantale homomorphism classes

This file defines morphisms between (additive) quantales

## Types of morphisms

* `AddQuantaleHom`: Additive quantale homomorphisms
* `QuantaleHom`: Quantale homomorphisms
* `ZeroAddQuantaleHom`: Additive unital quantale homomorphisms (i.e. on an additive monoid)
* `OneQuantaleHom`: Unital quantale homomorphisms (i.e. on a monoid)

As isomorphism, `OrderMonoidIso` - denoted `α ≃*o` works for both Quantales and OneQuantales,
and similar for the additive versions.

## Notation

* `→ₙ+q`: Bundled additive (non-unital) quantale homs.
* `→ₙ*q`: Bundled (non-unital) quantale homs.
* `→+q`: Bundled additive unital quantale homs.
* `→*q`: Bundled unital quantale homs.

## Implementation notes

The implementation follows largely the style of `Mathlib.Algebra.Order.Hom.Monoid`.

There's a coercion from bundled homs to fun, and the canonical notation is to use the bundled hom
as a function via this coercion.

In the file `Mathlib.Algebra.Order.Hom.Monoid` it is mentioned that there used to be classes:
`OrderAddMonoidHomClass` etc., but that in #10544 there was a migration from these typeclasses to
assumptions like `[FunLike F M N] [MonoidHomClass F M N] [OrderHomClass F M N]`.
We follow that approach here as well, and only define `AddQuantaleHom` without needing
`AddQuantaleHomClass`.

## Tags

quantale, ordered semigroup, complete lattice

## Todo

Why is there notation `→ₙ*` defined for non-unital Mul homomorphisms, but
no notation `→ₙ+` for non-unital Add homomorphisms? Create a PR for this?

Isomorphisms on quantales are simply `OrderAddMonoidIso` and `OrderMonoidIso`.
But it needs to be proven that both the iso and its inverse are OneQuantaleHom's.

-/

open Function

variable {F α β γ δ : Type*}

section AddQuantale

/-- `α →ₙ+q β` is the type of monotone functions `α → β` that preserve the `AddQuantale`
structure.

When possible, instead of parametrizing results over `(f : α →ₙ+q β)`,
you should parametrize over
`(F : Type*) [FunLike F M N] [AddHomClass F M N] [CompleteLatticeHomClass F M N] (f : F)`. -/
structure AddQuantaleHom (α β : Type*)
  [AddSemigroup α] [CompleteLattice α] [AddSemigroup β] [CompleteLattice β]
  extends AddHom α β, sSupHom α β

/-- Infix notation for `AddQuantaleHom`. -/
infixr:25 " →ₙ+q " => AddQuantaleHom

/-- `α →+q β` is the type of monotone functions `α → β` that preserve the `AddQuantale`
structure in case of a unital quantale.

When possible, instead of parametrizing results over `(f : α →+q β)`,
you should parametrize over
`(F : Type*) [FunLike F M N] [AddMonoidHomClass F M N] [CompleteLatticeHomClass F M N] (f : F)`. -/
structure ZeroAddQuantaleHom (α β : Type*)
  [AddMonoid α] [CompleteLattice α] [AddMonoid β] [CompleteLattice β]
  extends α →ₙ+q β, ZeroHom α β

/-- Infix notation for `ZeroAddQuantaleHom`. -/
infixr:25 " →+q " => ZeroAddQuantaleHom

-- Instances and lemmas are defined below through `@[to_additive]`.

end AddQuantale

section Quantale

/-- `α →ₙ*q β` is the type of monotone functions `α → β` that preserve the `Quantale`
structure.

When possible, instead of parametrizing results over `(f : α →ₙ*q β)`,
you should parametrize over
`(F : Type*) [FunLike F M N] [MulHomClass F M N] [CompleteLatticeHomClass F M N] (f : F)`. -/
@[to_additive]
structure QuantaleHom (α β : Type*)
  [Semigroup α] [CompleteLattice α] [Semigroup β] [CompleteLattice β]
  extends α →ₙ* β, sSupHom α β

/-- Infix notation for `AddQuantaleHom`. -/
infixr:25 " →ₙ*q " => QuantaleHom

/-- `α →*q β` is the type of monotone functions `α → β` that preserve the `AddQuantale`
structure in case of a unital quantale.

When possible, instead of parametrizing results over `(f : α →*q β)`,
you should parametrize over
`(F : Type*) [FunLike F M N] [MonoidHomClass F M N] [CompleteLatticeHomClass F M N] (f : F)`. -/
@[to_additive]
structure OneQuantaleHom (α β : Type*)
  [Monoid α] [CompleteLattice α] [Monoid β] [CompleteLattice β]
  extends α →ₙ*q β, OneHom α β

/-- Infix notation for `ZeroAddQuantaleHom`. -/
infixr:25 " →*q " => OneQuantaleHom

variable [Semigroup α] [Semigroup β] [CompleteLattice α] [CompleteLattice β] [FunLike F α β]

/-- Turn an element of a type `F` satisfying `MulHomClass F α β` and `sSupHomClass F α β`
into an actual `QuantaleHom`. This is declared as the default coercion from `F` to `α →ₙ*q β`. -/
@[to_additive (attr := coe)
  "Turn an element of a type `F` satisfying `AddHomClass F α β` and `sSupHomClass F α β`
into an actual `AddQuantaleHom`. This is declared as the default coercion from `F` to `α →ₙ+q β`."]
def QuantaleHomClass.toQuantaleHom [MulHomClass F α β] [sSupHomClass F α β] (f : F) :
    α →ₙ*q β := { (f : α →ₙ* β) with map_sSup' := sSupHomClass.map_sSup f }

/-- Any type satisfying `QuantaleHomClass` can be cast into `QuantaleHom` via
  `QuantaleHomClass.toQuantaleHom`. -/
@[to_additive "Any type satisfying `AddQuantaleHomClass` can be cast into `AddQuantaleHom` via
  `AddQuantaleHomClass.toAddQuantaleHom`."]
instance [MulHomClass F α β] [sSupHomClass F α β] : CoeTC F (α →ₙ*q β) :=
  ⟨QuantaleHomClass.toQuantaleHom⟩

end Quantale

section OneQuantale

variable [Monoid α] [Monoid β] [CompleteLattice α] [CompleteLattice β] [FunLike F α β]

/-- Turn an element of a type `F` satisfying `MonoidHomClass F α β` and `sSupHomClass F α β`
into an actual `OneQuantaleHom`. This is declared as the default coercion from `F` to `α →*q β`. -/
@[to_additive (attr := coe)
  "Turn an element of a type `F` satisfying `AddMonoidHomClass F α β` and `sSupHomClass F α β`
into an actual `ZeroAddQuantaleHom`. This is declared as the default coercion from `F` to
`α →+q β`."]
def OneQuantaleHomClass.toOneQuantaleHom [MonoidHomClass F α β] [sSupHomClass F α β] (f : F) :
    α →*q β := { (f : α →* β) with map_sSup' := sSupHomClass.map_sSup f }

/-- Any type satisfying `OneQuantaleHomClass` can be cast into `OneQuantaleHom` via
  `OneQuantaleHomClass.toOneQuantaleHom`. -/
@[to_additive "Any type satisfying `ZeroAddQuantaleHomClass` can be cast into `ZeroAddQuantaleHom`
  via `ZeroAddQuantaleHomClass.toZeroAddQuantaleHom`."]
instance [MonoidHomClass F α β] [sSupHomClass F α β] : CoeTC F (α →*q β) :=
  ⟨OneQuantaleHomClass.toOneQuantaleHom⟩

end OneQuantale

namespace QuantaleHom

variable [Semigroup α] [Semigroup β] [CompleteLattice α] [CompleteLattice β]
  [FunLike F α β] {f g : α →ₙ*q β}

@[to_additive]
instance : FunLike (α →ₙ*q β) α β where
  coe f := f.toFun
  coe_injective' f g h := by
    obtain ⟨⟨ _ ⟩, _⟩ := f
    obtain ⟨⟨ _ ⟩, _⟩ := g
    congr

@[to_additive]
instance : MulHomClass (α →ₙ*q β) α β where
  map_mul f _ _ := f.map_mul' _ _

@[to_additive]
instance : sSupHomClass (α →ₙ*q β) α β where
  map_sSup f := f.map_sSup'

-- Other lemmas should be accessed through the `FunLike` API
@[to_additive (attr := ext)]
theorem ext (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h

@[to_additive]
theorem toFun_eq_coe (f : α →ₙ*q β) : f.toFun = (f : α → β) :=
  rfl

end QuantaleHom

namespace OneQuantaleHom

variable [Monoid α] [Monoid β] [CompleteLattice α] [CompleteLattice β]
  [FunLike F α β] {f g : α →*q β}

@[to_additive]
instance : FunLike (α →*q β) α β where
  coe f := f.toFun
  coe_injective' f g h := by
    obtain ⟨⟨⟨_⟩,_⟩,_⟩ := f
    obtain ⟨⟨⟨_⟩,_⟩,_⟩ := g
    congr

@[to_additive]
instance : MonoidHomClass (α →*q β) α β where
  map_mul f _ _ := f.map_mul' _ _
  map_one f := f.map_one'

@[to_additive]
instance : sSupHomClass (α →*q β) α β where
  map_sSup f := f.map_sSup'

-- Other lemmas should be accessed through the `FunLike` API
@[to_additive (attr := ext)]
theorem ext (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h

@[to_additive]
theorem toFun_eq_coe (f : α →ₙ*q β) : f.toFun = (f : α → β) :=
  rfl

end OneQuantaleHom

namespace OrderMonoidIso

variable [Semigroup α] [Semigroup β] [CompleteLattice α] [CompleteLattice β]
  [FunLike F α β] {f g : α →ₙ*q β}

instance (f : α ≃*o β) : α →ₙ*q β where
  toFun := f.toFun
  map_mul' := f.map_mul'
  map_sSup' := sorry

end OrderMonoidIso
