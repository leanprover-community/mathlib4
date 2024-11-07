/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags
import Mathlib.Algebra.Order.Monoid.Canonical.Defs

/-! # Bundled ordered monoid structures on `Multiplicative α` and `Additive α`. -/

variable {α : Type*}

instance Multiplicative.orderedCommMonoid [OrderedAddCommMonoid α] :
    OrderedCommMonoid (Multiplicative α) :=
  { Multiplicative.partialOrder, Multiplicative.commMonoid with
    mul_le_mul_left := @OrderedAddCommMonoid.add_le_add_left α _ }

instance Additive.orderedAddCommMonoid [OrderedCommMonoid α] :
    OrderedAddCommMonoid (Additive α) :=
  { Additive.partialOrder, Additive.addCommMonoid with
    add_le_add_left := @OrderedCommMonoid.mul_le_mul_left α _ }

instance Multiplicative.orderedCancelAddCommMonoid [OrderedCancelAddCommMonoid α] :
    OrderedCancelCommMonoid (Multiplicative α) :=
  { Multiplicative.orderedCommMonoid with
    le_of_mul_le_mul_left := @OrderedCancelAddCommMonoid.le_of_add_le_add_left α _ }

instance Additive.orderedCancelAddCommMonoid [OrderedCancelCommMonoid α] :
    OrderedCancelAddCommMonoid (Additive α) :=
  { Additive.orderedAddCommMonoid with
    le_of_add_le_add_left := @OrderedCancelCommMonoid.le_of_mul_le_mul_left α _ }

instance Multiplicative.linearOrderedCommMonoid [LinearOrderedAddCommMonoid α] :
    LinearOrderedCommMonoid (Multiplicative α) :=
  { Multiplicative.linearOrder, Multiplicative.orderedCommMonoid with }

instance Additive.linearOrderedAddCommMonoid [LinearOrderedCommMonoid α] :
    LinearOrderedAddCommMonoid (Additive α) :=
  { Additive.linearOrder, Additive.orderedAddCommMonoid with }

instance Multiplicative.canonicallyOrderedCommMonoid [CanonicallyOrderedAddCommMonoid α] :
    CanonicallyOrderedCommMonoid (Multiplicative α) :=
  { Multiplicative.orderedCommMonoid, Multiplicative.orderBot,
    Multiplicative.existsMulOfLe with le_self_mul := @le_self_add α _ }

instance Additive.canonicallyOrderedAddCommMonoid [CanonicallyOrderedCommMonoid α] :
    CanonicallyOrderedAddCommMonoid (Additive α) :=
  { Additive.orderedAddCommMonoid, Additive.orderBot, Additive.existsAddOfLe with
    le_self_add := @le_self_mul α _ }

instance Multiplicative.canonicallyLinearOrderedCommMonoid
    [CanonicallyLinearOrderedAddCommMonoid α] :
    CanonicallyLinearOrderedCommMonoid (Multiplicative α) :=
  { Multiplicative.canonicallyOrderedCommMonoid, Multiplicative.linearOrder with }

instance [CanonicallyLinearOrderedCommMonoid α] :
    CanonicallyLinearOrderedAddCommMonoid (Additive α) :=
  { Additive.canonicallyOrderedAddCommMonoid, Additive.linearOrder with }
