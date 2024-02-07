/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Mathlib.Algebra.Group.TypeTags
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Canonical.Defs

#align_import algebra.order.monoid.type_tags from "leanprover-community/mathlib"@"2258b40dacd2942571c8ce136215350c702dc78f"

/-! # Ordered monoid structures on `Multiplicative α` and `Additive α`. -/

set_option autoImplicit true

instance (priority := 10000) : ∀ [LE α], LE (Multiplicative α) :=
  fun {inst} => inst

instance (priority := 10000) : ∀ [LE α], LE (Additive α) :=
  fun {inst} => inst

instance (priority := 10000) : ∀ [LT α], LT (Multiplicative α) :=
  fun {inst} => inst

instance (priority := 10000) : ∀ [LT α], LT (Additive α) :=
  fun {inst} => inst

instance (priority := 10000) Multiplicative.preorder : ∀ [Preorder α], Preorder (Multiplicative α) :=
  fun {inst} => inst

instance (priority := 10000) Additive.preorder : ∀ [Preorder α], Preorder (Additive α) :=
  fun {inst} => inst

instance (priority := 10000) Multiplicative.partialOrder : ∀ [PartialOrder α], PartialOrder (Multiplicative α) :=
  fun {inst} => inst

instance (priority := 10000) Additive.partialOrder : ∀ [PartialOrder α], PartialOrder (Additive α) :=
  fun {inst} => inst

instance (priority := 10000) Multiplicative.linearOrder : ∀ [LinearOrder α], LinearOrder (Multiplicative α) :=
  fun {inst} => inst

instance (priority := 10000) Additive.linearOrder : ∀ [LinearOrder α], LinearOrder (Additive α) :=
  fun {inst} => inst

instance (priority := 10000) Multiplicative.orderBot [LE α] : ∀ [OrderBot α], OrderBot (Multiplicative α) :=
  fun {inst} => inst

instance (priority := 10000) Additive.orderBot [LE α] : ∀ [OrderBot α], OrderBot (Additive α) :=
  fun {inst} => inst

instance (priority := 10000) Multiplicative.orderTop [LE α] : ∀ [OrderTop α], OrderTop (Multiplicative α) :=
  fun {inst} => inst

instance (priority := 10000) Additive.orderTop [LE α] : ∀ [OrderTop α], OrderTop (Additive α) :=
  fun {inst} => inst

instance (priority := 10000) Multiplicative.boundedOrder [LE α] : ∀ [BoundedOrder α], BoundedOrder (Multiplicative α) :=
  fun {inst} => inst

instance (priority := 10000) Additive.boundedOrder [LE α] : ∀ [BoundedOrder α], BoundedOrder (Additive α) :=
  fun {inst} => inst

instance (priority := 10000) Multiplicative.orderedCommMonoid [OrderedAddCommMonoid α] :
    OrderedCommMonoid (Multiplicative α) :=
  { Multiplicative.partialOrder, Multiplicative.commMonoid with
    mul_le_mul_left := @OrderedAddCommMonoid.add_le_add_left α _ }

instance (priority := 10000) Additive.orderedAddCommMonoid [OrderedCommMonoid α] :
    OrderedAddCommMonoid (Additive α) :=
  { Additive.partialOrder, Additive.addCommMonoid with
    add_le_add_left := @OrderedCommMonoid.mul_le_mul_left α _ }

instance (priority := 10000) Multiplicative.orderedCancelAddCommMonoid [OrderedCancelAddCommMonoid α] :
    OrderedCancelCommMonoid (Multiplicative α) :=
  { Multiplicative.orderedCommMonoid with
    le_of_mul_le_mul_left := @OrderedCancelAddCommMonoid.le_of_add_le_add_left α _ }

instance (priority := 10000) Additive.orderedCancelAddCommMonoid [OrderedCancelCommMonoid α] :
    OrderedCancelAddCommMonoid (Additive α) :=
  { Additive.orderedAddCommMonoid with
    le_of_add_le_add_left := @OrderedCancelCommMonoid.le_of_mul_le_mul_left α _ }

instance (priority := 10000) Multiplicative.linearOrderedCommMonoid [LinearOrderedAddCommMonoid α] :
    LinearOrderedCommMonoid (Multiplicative α) :=
  { Multiplicative.linearOrder, Multiplicative.orderedCommMonoid with }

instance (priority := 10000) Additive.linearOrderedAddCommMonoid [LinearOrderedCommMonoid α] :
    LinearOrderedAddCommMonoid (Additive α) :=
  { Additive.linearOrder, Additive.orderedAddCommMonoid with }

instance (priority := 10000) Multiplicative.existsMulOfLe [Add α] [LE α] [ExistsAddOfLE α] :
    ExistsMulOfLE (Multiplicative α) :=
  ⟨@exists_add_of_le α _ _ _⟩

instance (priority := 10000) Additive.existsAddOfLe [Mul α] [LE α] [ExistsMulOfLE α] : ExistsAddOfLE (Additive α) :=
  ⟨@exists_mul_of_le α _ _ _⟩

instance (priority := 10000) Multiplicative.canonicallyOrderedCommMonoid [CanonicallyOrderedAddCommMonoid α] :
    CanonicallyOrderedCommMonoid (Multiplicative α) :=
  { Multiplicative.orderedCommMonoid, Multiplicative.orderBot,
    Multiplicative.existsMulOfLe with le_self_mul := @le_self_add α _ }

instance (priority := 10000) Additive.canonicallyOrderedAddCommMonoid [CanonicallyOrderedCommMonoid α] :
    CanonicallyOrderedAddCommMonoid (Additive α) :=
  { Additive.orderedAddCommMonoid, Additive.orderBot, Additive.existsAddOfLe with
    le_self_add := @le_self_mul α _ }

instance (priority := 10000) Multiplicative.canonicallyLinearOrderedCommMonoid
    [CanonicallyLinearOrderedAddCommMonoid α] :
    CanonicallyLinearOrderedCommMonoid (Multiplicative α) :=
  { Multiplicative.canonicallyOrderedCommMonoid, Multiplicative.linearOrder with }

instance (priority := 10000) [CanonicallyLinearOrderedCommMonoid α] :
    CanonicallyLinearOrderedAddCommMonoid (Additive α) :=
  { Additive.canonicallyOrderedAddCommMonoid, Additive.linearOrder with }

namespace Additive

variable [Preorder α]

@[simp]
theorem ofMul_le {a b : α} : ofMul a ≤ ofMul b ↔ a ≤ b :=
  Iff.rfl
#align additive.of_mul_le Additive.ofMul_le

@[simp]
theorem ofMul_lt {a b : α} : ofMul a < ofMul b ↔ a < b :=
  Iff.rfl
#align additive.of_mul_lt Additive.ofMul_lt

@[simp]
theorem toMul_le {a b : Additive α} : toMul a ≤ toMul b ↔ a ≤ b :=
  Iff.rfl
#align additive.to_mul_le Additive.toMul_le

@[simp]
theorem toMul_lt {a b : Additive α} : toMul a < toMul b ↔ a < b :=
  Iff.rfl
#align additive.to_mul_lt Additive.toMul_lt

end Additive

namespace Multiplicative

variable [Preorder α]

@[simp]
theorem ofAdd_le {a b : α} : ofAdd a ≤ ofAdd b ↔ a ≤ b :=
  Iff.rfl
#align multiplicative.of_add_le Multiplicative.ofAdd_le

@[simp]
theorem ofAdd_lt {a b : α} : ofAdd a < ofAdd b ↔ a < b :=
  Iff.rfl
#align multiplicative.of_add_lt Multiplicative.ofAdd_lt

@[simp]
theorem toAdd_le {a b : Multiplicative α} : toAdd a ≤ toAdd b ↔ a ≤ b :=
  Iff.rfl
#align multiplicative.to_add_le Multiplicative.toAdd_le

@[simp]
theorem toAdd_lt {a b : Multiplicative α} : toAdd a < toAdd b ↔ a < b :=
  Iff.rfl
#align multiplicative.to_add_lt Multiplicative.toAdd_lt

end Multiplicative
