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

This file defines the bundled structures for lax and oplax unital (additive) quantale homomorphisms.
Namely, we define `LaxQuantaleHom` (resp., `LaxAddQuantaleHom`) to be bundled subadditive
homomorphisms between multiplicative (resp.,additive) quantales, and `OplaxQuantaleHom`
(resp., `OplaxAddQuantaleHom`) to be bundled superadditive homomorphisms between multiplicative
(resp. additive) unital quantales.

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
