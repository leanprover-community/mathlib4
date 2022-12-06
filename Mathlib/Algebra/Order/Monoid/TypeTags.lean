/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Mathbin.Algebra.Group.TypeTags
import Mathbin.Algebra.Order.Monoid.Cancel.Defs
import Mathbin.Algebra.Order.Monoid.Canonical.Defs

/-! # Ordered monoid structures on `multiplicative α` and `additive α`. -/


universe u

variable {α : Type u}

instance : ∀ [LE α], LE (Multiplicative α) :=
  id

instance : ∀ [LE α], LE (Additive α) :=
  id

instance : ∀ [LT α], LT (Multiplicative α) :=
  id

instance : ∀ [LT α], LT (Additive α) :=
  id

instance : ∀ [Preorder α], Preorder (Multiplicative α) :=
  id

instance : ∀ [Preorder α], Preorder (Additive α) :=
  id

instance : ∀ [PartialOrder α], PartialOrder (Multiplicative α) :=
  id

instance : ∀ [PartialOrder α], PartialOrder (Additive α) :=
  id

instance : ∀ [LinearOrder α], LinearOrder (Multiplicative α) :=
  id

instance : ∀ [LinearOrder α], LinearOrder (Additive α) :=
  id

instance [LE α] : ∀ [OrderBot α], OrderBot (Multiplicative α) :=
  id

instance [LE α] : ∀ [OrderBot α], OrderBot (Additive α) :=
  id

instance [LE α] : ∀ [OrderTop α], OrderTop (Multiplicative α) :=
  id

instance [LE α] : ∀ [OrderTop α], OrderTop (Additive α) :=
  id

instance [LE α] : ∀ [BoundedOrder α], BoundedOrder (Multiplicative α) :=
  id

instance [LE α] : ∀ [BoundedOrder α], BoundedOrder (Additive α) :=
  id

instance [OrderedAddCommMonoid α] : OrderedCommMonoid (Multiplicative α) :=
  { Multiplicative.partialOrder, Multiplicative.commMonoid with
    mul_le_mul_left := @OrderedAddCommMonoid.add_le_add_left α _ }

instance [OrderedCommMonoid α] : OrderedAddCommMonoid (Additive α) :=
  { Additive.partialOrder, Additive.addCommMonoid with
    add_le_add_left := @OrderedCommMonoid.mul_le_mul_left α _ }

instance [OrderedCancelAddCommMonoid α] : OrderedCancelCommMonoid (Multiplicative α) :=
  { Multiplicative.orderedCommMonoid with
    le_of_mul_le_mul_left := @OrderedCancelAddCommMonoid.le_of_add_le_add_left α _ }

instance [OrderedCancelCommMonoid α] : OrderedCancelAddCommMonoid (Additive α) :=
  { Additive.orderedAddCommMonoid with
    le_of_add_le_add_left := @OrderedCancelCommMonoid.le_of_mul_le_mul_left α _ }

instance [LinearOrderedAddCommMonoid α] : LinearOrderedCommMonoid (Multiplicative α) :=
  { Multiplicative.linearOrder, Multiplicative.orderedCommMonoid with }

instance [LinearOrderedCommMonoid α] : LinearOrderedAddCommMonoid (Additive α) :=
  { Additive.linearOrder, Additive.orderedAddCommMonoid with }

instance [Add α] [LE α] [HasExistsAddOfLe α] : HasExistsMulOfLe (Multiplicative α) :=
  ⟨@exists_add_of_le α _ _ _⟩

instance [Mul α] [LE α] [HasExistsMulOfLe α] : HasExistsAddOfLe (Additive α) :=
  ⟨@exists_mul_of_le α _ _ _⟩

instance [CanonicallyOrderedAddMonoid α] : CanonicallyOrderedMonoid (Multiplicative α) :=
  { Multiplicative.orderedCommMonoid, Multiplicative.orderBot,
    Multiplicative.has_exists_mul_of_le with le_self_mul := @le_self_add α _ }

instance [CanonicallyOrderedMonoid α] : CanonicallyOrderedAddMonoid (Additive α) :=
  { Additive.orderedAddCommMonoid, Additive.orderBot, Additive.has_exists_add_of_le with
    le_self_add := @le_self_mul α _ }

instance [CanonicallyLinearOrderedAddMonoid α] :
    CanonicallyLinearOrderedMonoid (Multiplicative α) :=
  { Multiplicative.canonicallyOrderedMonoid, Multiplicative.linearOrder with }

instance [CanonicallyLinearOrderedMonoid α] : CanonicallyLinearOrderedAddMonoid (Additive α) :=
  { Additive.canonicallyOrderedAddMonoid, Additive.linearOrder with }

namespace Additive

variable [Preorder α]

@[simp]
theorem of_mul_le {a b : α} : ofMul a ≤ ofMul b ↔ a ≤ b :=
  Iff.rfl
#align additive.of_mul_le Additive.of_mul_le

@[simp]
theorem of_mul_lt {a b : α} : ofMul a < ofMul b ↔ a < b :=
  Iff.rfl
#align additive.of_mul_lt Additive.of_mul_lt

@[simp]
theorem to_mul_le {a b : Additive α} : toMul a ≤ toMul b ↔ a ≤ b :=
  Iff.rfl
#align additive.to_mul_le Additive.to_mul_le

@[simp]
theorem to_mul_lt {a b : Additive α} : toMul a < toMul b ↔ a < b :=
  Iff.rfl
#align additive.to_mul_lt Additive.to_mul_lt

end Additive

namespace Multiplicative

variable [Preorder α]

@[simp]
theorem of_add_le {a b : α} : ofAdd a ≤ ofAdd b ↔ a ≤ b :=
  Iff.rfl
#align multiplicative.of_add_le Multiplicative.of_add_le

@[simp]
theorem of_add_lt {a b : α} : ofAdd a < ofAdd b ↔ a < b :=
  Iff.rfl
#align multiplicative.of_add_lt Multiplicative.of_add_lt

@[simp]
theorem to_add_le {a b : Multiplicative α} : toAdd a ≤ toAdd b ↔ a ≤ b :=
  Iff.rfl
#align multiplicative.to_add_le Multiplicative.to_add_le

@[simp]
theorem to_add_lt {a b : Multiplicative α} : toAdd a < toAdd b ↔ a < b :=
  Iff.rfl
#align multiplicative.to_add_lt Multiplicative.to_add_lt

end Multiplicative

