/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl

! This file was ported from Lean 3 source module algebra.order.monoid.type_tags
! leanprover-community/mathlib commit f1a2caaf51ef593799107fe9a8d5e411599f3996
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.Group.TypeTags
import Mathlib.Algebra.Order.Monoid.Cancel.Defs
import Mathlib.Algebra.Order.Monoid.Canonical.Defs

/-! # Ordered monoid structures on `Multiplicative α` and `Additive α`. -/


instance [LE α] : LE (Multiplicative α) where
  le x y := x.1 ≤ y.1

instance [LE α] : LE (Additive α) where
  le x y := x.1 ≤ y.1

instance [LE α] [DecidableRel ((· ≤ ·) : α → α → Prop)] :
    DecidableRel ((· ≤ ·) : Multiplicative α → Multiplicative α → Prop) :=
  fun x y => (inferInstance : Decidable (x.1 ≤ y.1))

instance [LE α] [DecidableRel ((· ≤ ·) : α → α → Prop)] :
    DecidableRel ((· ≤ ·) : Additive α → Additive α → Prop) :=
  fun x y => (inferInstance : Decidable (x.1 ≤ y.1))

instance [LT α] : LT (Multiplicative α) where
  lt x y := x.1 < y.1

instance [LT α] : LT (Additive α) where
  lt x y := x.1 < y.1

instance [LT α] [DecidableRel ((· < ·) : α → α → Prop)] :
    DecidableRel ((· < ·) : Multiplicative α → Multiplicative α → Prop) :=
  fun x y => (inferInstance : Decidable (x.1 < y.1))

instance [LT α] [DecidableRel ((· < ·) : α → α → Prop)] :
    DecidableRel ((· < ·) : Additive α → Additive α → Prop) :=
  fun x y => (inferInstance : Decidable (x.1 < y.1))

instance Multiplicative.preorder [Preorder α] : Preorder (Multiplicative α) :=
  Preorder.lift toAdd

instance Additive.preorder [Preorder α] : Preorder (Additive α) :=
  Preorder.lift toMul

instance Multiplicative.partialOrder [PartialOrder α] : PartialOrder (Multiplicative α) :=
  PartialOrder.lift toAdd toAdd_injective

instance Additive.partialOrder [PartialOrder α] : PartialOrder (Additive α) :=
  PartialOrder.lift toMul toMul_injective

instance Multiplicative.HasSup [HasSup α] : HasSup (Multiplicative α) where
  sup x y := ⟨x.1 ⊔ y.1⟩

instance Multiplicative.HasInf [HasInf α] : HasInf (Multiplicative α) where
  inf x y := ⟨x.1 ⊓ y.1⟩

instance Additive.HasSup [HasSup α] : HasSup (Additive α) where
  sup x y := ⟨x.1 ⊔ y.1⟩

instance Additive.HasInf [HasInf α] : HasInf (Additive α) where
  inf x y := ⟨x.1 ⊓ y.1⟩

instance Multiplicative.linearOrder [LinearOrder α] : LinearOrder (Multiplicative α) :=
  LinearOrder.lift toAdd toAdd_injective (fun _ _ => rfl) fun _ _ => rfl

instance Additive.linearOrder [LinearOrder α] : LinearOrder (Additive α) :=
  LinearOrder.lift toMul toMul_injective (fun _ _ => rfl) fun _ _ => rfl

instance Multiplicative.bot [Bot α] : Bot (Multiplicative α) where
  bot := ⟨⊥⟩

instance Additive.bot [Bot α] : Bot (Additive α) where
  bot := ⟨⊥⟩

instance Multiplicative.top [Top α] : Top (Multiplicative α) where
  top := ⟨⊤⟩

instance Additive.top [Top α] : Top (Additive α) where
  top := ⟨⊤⟩

instance Multiplicative.orderBot [LE α] [OrderBot α] : OrderBot (Multiplicative α) :=
  OrderBot.lift toAdd (fun _ _ => id) rfl

instance Additive.orderBot [LE α] [OrderBot α] : OrderBot (Additive α) :=
  OrderBot.lift toMul (fun _ _ => id) rfl

instance Multiplicative.orderTop [LE α] [OrderTop α] : OrderTop (Multiplicative α) :=
  OrderTop.lift toAdd (fun _ _ => id) rfl

instance Additive.orderTop [LE α] [OrderTop α] : OrderTop (Additive α) :=
  OrderTop.lift toMul (fun _ _ => id) rfl

instance Multiplicative.boundedOrder [LE α] [BoundedOrder α] : BoundedOrder (Multiplicative α) :=
  ⟨⟩

instance Additive.boundedOrder [LE α] [BoundedOrder α] : BoundedOrder (Additive α) :=
  ⟨⟩

namespace Additive

variable [LE α] [LT α] [Bot α] [Top α]

@[simp]
theorem ofMul_le {a b : α} : ofMul a ≤ ofMul b ↔ a ≤ b :=
  Iff.rfl
#align additive.of_mul_le Additive.ofMul_le

@[simp]
theorem toMul_le {a b : Additive α} : toMul a ≤ toMul b ↔ a ≤ b :=
  Iff.rfl
#align additive.to_mul_le Additive.toMul_le

@[simp]
theorem ofMul_lt {a b : α} : ofMul a < ofMul b ↔ a < b :=
  Iff.rfl
#align additive.of_mul_lt Additive.ofMul_lt

@[simp]
theorem toMul_lt {a b : Additive α} : toMul a < toMul b ↔ a < b :=
  Iff.rfl
#align additive.to_mul_lt Additive.toMul_lt

@[simp] theorem toMul_bot : toMul (⊥ : Additive α) = ⊥ := rfl
@[simp] theorem ofMul_bot : ofMul (⊥ : α) = ⊥ := rfl
@[simp] theorem toMul_top : toMul (⊤ : Additive α) = ⊤ := rfl
@[simp] theorem ofMul_top : ofMul (⊤ : α) = ⊤ := rfl

end Additive

namespace Multiplicative

variable [LE α] [LT α] [Bot α] [Top α]

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

@[simp] theorem toAdd_bot : toAdd (⊥ : Multiplicative α) = ⊥ := rfl
@[simp] theorem ofAdd_bot : ofAdd (⊥ : α) = ⊥ := rfl
@[simp] theorem toAdd_top : toAdd (⊤ : Multiplicative α) = ⊤ := rfl
@[simp] theorem ofAdd_top : ofAdd (⊤ : α) = ⊤ := rfl

end Multiplicative

instance Multiplicative.orderedCommMonoid [OrderedAddCommMonoid α] :
    OrderedCommMonoid (Multiplicative α) :=
  { Multiplicative.partialOrder, Multiplicative.commMonoid with
    mul_le_mul_left := fun _ _ h _ ↦ add_le_add_left (toAdd_le.2 h) _ }

instance Additive.orderedAddCommMonoid [OrderedCommMonoid α] :
    OrderedAddCommMonoid (Additive α) :=
  { Additive.partialOrder, Additive.addCommMonoid with
    add_le_add_left := fun _ _ h _ ↦ mul_le_mul_left' (toMul_le.2 h) _ }

instance Multiplicative.orderedCancelAddCommMonoid [OrderedCancelAddCommMonoid α] :
    OrderedCancelCommMonoid (Multiplicative α) :=
  { Multiplicative.orderedCommMonoid with
    le_of_mul_le_mul_left := fun _ _ _ ↦ toAdd_le.1 ∘ le_of_add_le_add_left }

instance Additive.orderedCancelAddCommMonoid [OrderedCancelCommMonoid α] :
    OrderedCancelAddCommMonoid (Additive α) :=
  { Additive.orderedAddCommMonoid with
    le_of_add_le_add_left := fun _ _ _ ↦ toMul_le.1 ∘ le_of_mul_le_mul_left' }

instance Multiplicative.linearOrderedCommMonoid [LinearOrderedAddCommMonoid α] :
    LinearOrderedCommMonoid (Multiplicative α) :=
  { Multiplicative.linearOrder, Multiplicative.orderedCommMonoid with }

instance Additive.linearOrderedAddCommMonoid [LinearOrderedCommMonoid α] :
    LinearOrderedAddCommMonoid (Additive α) :=
  { Additive.linearOrder, Additive.orderedAddCommMonoid with }

instance Multiplicative.existsMulOfLe [Add α] [LE α] [ExistsAddOfLE α] :
    ExistsMulOfLE (Multiplicative α) :=
  ⟨fun h => let ⟨c, hc⟩ := exists_add_of_le (toAdd_le.2 h); ⟨⟨c⟩, toAdd_injective hc⟩⟩

instance Additive.existsAddOfLe [Mul α] [LE α] [ExistsMulOfLE α] : ExistsAddOfLE (Additive α) :=
  ⟨fun h => let ⟨c, hc⟩ := exists_mul_of_le (toMul_le.2 h); ⟨⟨c⟩, toMul_injective hc⟩⟩

instance Multiplicative.canonicallyOrderedMonoid [CanonicallyOrderedAddMonoid α] :
    CanonicallyOrderedMonoid (Multiplicative α) :=
  { Multiplicative.orderedCommMonoid, Multiplicative.orderBot, Multiplicative.existsMulOfLe with
    le_self_mul := fun _ _ ↦ toAdd_le.1 le_self_add }

instance Additive.canonicallyOrderedAddMonoid [CanonicallyOrderedMonoid α] :
    CanonicallyOrderedAddMonoid (Additive α) :=
  { Additive.orderedAddCommMonoid, Additive.orderBot, Additive.existsAddOfLe with
    le_self_add := fun _ _ ↦ toMul_le.1 le_self_mul }

instance Multiplicative.canonicallyLinearOrderedMonoid [CanonicallyLinearOrderedAddMonoid α] :
    CanonicallyLinearOrderedMonoid (Multiplicative α) :=
  { Multiplicative.canonicallyOrderedMonoid, Multiplicative.linearOrder with }

instance [CanonicallyLinearOrderedMonoid α] : CanonicallyLinearOrderedAddMonoid (Additive α) :=
  { Additive.canonicallyOrderedAddMonoid, Additive.linearOrder with }
