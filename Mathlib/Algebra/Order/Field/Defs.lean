/-
Copyright (c) 2014 Robert Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Lewis, Leonardo de Moura, Mario Carneiro, Floris van Doorn
-/
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Field.Defs

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
-/

-- Guard against import creep.
assert_not_exists MonoidHom

variable {α : Type*}

/-- A linear ordered semifield is a field with a linear order respecting the operations. -/
class LinearOrderedSemifield (α : Type*) extends LinearOrderedCommSemiring α, Semifield α
#align linear_ordered_semifield LinearOrderedSemifield

/-- A linear ordered field is a field with a linear order respecting the operations. -/
class LinearOrderedField (α : Type*) extends LinearOrderedCommRing α, Field α
#align linear_ordered_field LinearOrderedField

-- See note [lower instance priority]
instance (priority := 100) LinearOrderedField.toLinearOrderedSemifield [LinearOrderedField α] :
    LinearOrderedSemifield α :=
  { LinearOrderedRing.toLinearOrderedSemiring, ‹LinearOrderedField α› with }
#align linear_ordered_field.to_linear_ordered_semifield LinearOrderedField.toLinearOrderedSemifield

