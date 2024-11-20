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
-/

open Function

variable {F α β γ δ : Type*}

section AddQuantale

/-- `α →ₙ+q β` is the type of monotone functions `α → β` that preserve the `AddQuantale`
structure.

When possible, instead of parametrizing results over `(f : α →ₙ+q β)`,
you should parametrize over
`(F : Type*) [FunLike F M N] [MulHomClass F M N] [CompleteLatticeHomClass F M N] (f : F)`. -/
structure AddQuantaleHom (α β : Type*)
  [AddSemigroup α] [CompleteLattice α] [AddSemigroup β] [CompleteLattice β]
  extends AddHom α β, CompleteLatticeHom α β

/-- Infix notation for `AddQuantaleHom`. -/
infixr:25 " →ₙ+q " => AddQuantaleHom

/-- `α ≃+q β` is the type of monotone isomorphisms `α ≃ β` that preserve the `AddQuantale`
structure.

When possible, instead of parametrizing results over `(f : α ≃+q β)`,
you should parametrize over
`(F : Type*) [FunLike F M N] [AddEquivClass F M N] [OrderIsoClass F M N] (f : F)`. -/
structure AddQuantaleIso (α β : Type*)
  [AddSemigroup α] [CompleteLattice α] [AddSemigroup β] [CompleteLattice β]
  extends α ≃+ β, α ≃o β where

/-- Infix notation for `AddQuantaleIso`. -/
infixr:25 " ≃+q " => AddQuantaleIso

-- Instances and lemmas are defined below through `@[to_additive]`.

end AddQuantale

/-
## Doubt!

In `Mathlib.Algebra.Order.Hom.Monoid` the definition of `OrderAddMonoidHom` seems to
not depend on the `[AddZeroClass α]` and `[AddZeroClass β]` assumption at all. If those
would be left out, a better name would be `OrderAddSemigroupHom` and the resulting
`OrderAddSemigroupIso` would be the appropriate isomorphism for `Quantales` as well,
i.e. we would not have to worry about isomorphisms at all in this file.

An `OrderAddSemigroupHom` is not a `AddQuantaleHom` because the `Sup` is not preserved,
but for isomorhpisms this is the case.

My worry, only, is that `OrderAddSemigroupHom` applied to `Monoids` does not preserve
the unit/zero element. So it could be that there is something missing in the definitions
in `Mathlib.Algebra.Order.Hom.Monoid`.

## Other notes:

Why is there notation `→ₙ*` defined for non-unital Mul homomorphisms, but
no notation `→ₙ+` for non-unital Add homomorphisms?

-/
