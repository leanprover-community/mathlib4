/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Simon Hudon, Mario Carneiro
-/
module

public import Mathlib.Algebra.Group.Defs

/-!
# Commutative structures from unbundled commutativity

This file used to provide scoped instances promoting algebraic structures satisfying
`IsMulCommutative` or `IsAddCommutative` to their bundled commutative counterparts
(`CommMagma`, `CommSemigroup`, `CommMonoid`, `DivisionCommMonoid`, `CommGroup`).

In the `IsMulCommutative` unbundling experiment those bundled commutative classes no longer
exist: commutativity is carried by the Prop mixins `IsMulCommutative` / `IsAddCommutative`
(defined in `Mathlib.Algebra.Group.Semigroup`) alongside the non-commutative sibling classes,
so no promotion instances are needed.
-/

@[expose] public section

assert_not_exists MonoidWithZero DenselyOrdered Function.const_injective
