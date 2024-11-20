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

Isomorphisms on quantales are simply `OrderAddIso` and `OrderMulIso`,
but `Mathlib.Algebra.Order.Hom` needs to be updated to support this.
Create a PR for this?

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
  extends α →+ β, sSupHom α β

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
structure OneQuantaleHom (α β : Type*)
  [Monoid α] [CompleteLattice α] [Monoid β] [CompleteLattice β]
  extends α →* β, sSupHom α β

/-- Infix notation for `ZeroAddQuantaleHom`. -/
infixr:25 " →*q " => OneQuantaleHom

end Quantale
