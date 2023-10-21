/-
Copyright (c) 2014 Robert Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Lewis, Leonardo de Moura, Mario Carneiro, Floris van Doorn
-/
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Order.Ring.Defs

#align_import algebra.order.field.defs from "leanprover-community/mathlib"@"655994e298904d7e5bbd1e18c95defd7b543eb94"

/-!
# Linear ordered (semi)fields

A linear ordered (semi)field is a (semi)field equipped with a linear order such that
* addition respects the order: `a ≤ b → c + a ≤ c + b`;
* multiplication of positives is positive: `0 < a → 0 < b → 0 < a * b`;
* `0 < 1`.

## Main Definitions

* `LinearOrderedSemifield`: Typeclass for linear order semifields.
* `LinearOrderedField`: Typeclass for linear ordered fields.

## Implementation details

For olean caching reasons, this file is separate to the main file,
`Mathlib.Algebra.Order.Field.Basic`. The lemmata are instead located there.

-/


variable {α : Type*}

/-- A linear ordered semifield is a field with a linear order respecting the operations. -/
class LinearOrderedSemifield (α : Type*) extends Semifield α, LinearOrderedCommSemiring α
#align linear_ordered_semifield LinearOrderedSemifield

attribute [instance 50] LinearOrderedSemifield.toSemifield
attribute [instance 100] LinearOrderedSemifield.toLinearOrderedCommSemiring
attribute [instance 0] LinearOrderedSemifield.toPartialOrder
attribute [instance 0] LinearOrderedSemifield.toMin
attribute [instance 0] LinearOrderedSemifield.toMax
attribute [instance 0] LinearOrderedSemifield.toOrd

/-- A linear ordered field is a field with a linear order respecting the operations. -/
class LinearOrderedField (α : Type*) extends Field α, LinearOrderedCommRing α
#align linear_ordered_field LinearOrderedField

attribute [instance 50] LinearOrderedField.toField
attribute [instance 100] LinearOrderedField.toLinearOrderedCommRing
attribute [instance 0] LinearOrderedField.toPartialOrder
attribute [instance 0] LinearOrderedField.toMin
attribute [instance 0] LinearOrderedField.toMax
attribute [instance 0] LinearOrderedField.toOrd

-- See note [lower instance priority]
instance (priority := 100) LinearOrderedField.toLinearOrderedSemifield [LinearOrderedField α] :
    LinearOrderedSemifield α :=
  { LinearOrderedRing.toLinearOrderedSemiring, ‹LinearOrderedField α› with }
#align linear_ordered_field.to_linear_ordered_semifield LinearOrderedField.toLinearOrderedSemifield

-- Guard against import creep.
assert_not_exists MonoidHom
