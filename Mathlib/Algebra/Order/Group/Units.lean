/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
module

public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Units

set_option doc.verso true
set_option doc.verso.suggestions false

/-!
# The units of an ordered commutative monoid form an ordered commutative group
-/

public section


variable {α : Type*}

/-- The units of an ordered commutative monoid form an ordered commutative group. -/
@[to_additive
      /-- The units of an ordered commutative additive monoid form an ordered commutative
      additive group. -/]
instance Units.isOrderedMonoid [CommMonoid α] [Preorder α] [IsOrderedMonoid α] :
    IsOrderedMonoid αˣ where
  mul_le_mul_left _ _ h _ := mul_le_mul_left (α := α) h _
