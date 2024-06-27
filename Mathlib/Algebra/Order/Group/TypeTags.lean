/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Monoid.TypeTags

#align_import algebra.order.group.type_tags from "leanprover-community/mathlib"@"2258b40dacd2942571c8ce136215350c702dc78f"

/-! # Ordered group structures on `Multiplicative α` and `Additive α`. -/


variable {α : Type*}

instance Multiplicative.orderedCommGroup [AddCommGroup α] [OrderedAddCommGroup α] :
    OrderedCommGroup (Multiplicative α) :=
  { Multiplicative.commGroup (α := α), Multiplicative.orderedCommMonoid with }

instance Additive.orderedAddCommGroup [CommGroup α] [OrderedCommGroup α] :
    OrderedAddCommGroup (Additive α) :=
  { Additive.addCommGroup (α := α), Additive.orderedAddCommMonoid with }

instance Multiplicative.linearOrderedCommGroup [AddCommGroup α] [LinearOrderedAddCommGroup α] :
    LinearOrderedCommGroup (Multiplicative α) :=
  { Multiplicative.linearOrder, Multiplicative.orderedCommGroup with }

instance Additive.linearOrderedAddCommGroup [CommGroup α] [LinearOrderedCommGroup α] :
    LinearOrderedAddCommGroup (Additive α) :=
  { Additive.linearOrder, Additive.orderedAddCommGroup with }
