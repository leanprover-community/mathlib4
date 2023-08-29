/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Mathlib.Algebra.Group.WithOne.Defs
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.ZeroLEOne

#align_import algebra.order.monoid.with_zero.defs from "leanprover-community/mathlib"@"4dc134b97a3de65ef2ed881f3513d56260971562"

/-!
# Adjoining a zero element to an ordered monoid.
-/


universe u

variable {α : Type u}

/-- A linearly ordered commutative monoid with a zero element. -/
class LinearOrderedCommMonoidWithZero (α : Type*) extends LinearOrderedCommMonoid α,
  CommMonoidWithZero α where
  /-- `0 ≤ 1` in any linearly ordered commutative monoid. -/
  zero_le_one : (0 : α) ≤ 1
#align linear_ordered_comm_monoid_with_zero LinearOrderedCommMonoidWithZero

instance (priority := 100) LinearOrderedCommMonoidWithZero.toZeroLeOneClass
    [LinearOrderedCommMonoidWithZero α] : ZeroLEOneClass α :=
  { ‹LinearOrderedCommMonoidWithZero α› with }
#align linear_ordered_comm_monoid_with_zero.to_zero_le_one_class LinearOrderedCommMonoidWithZero.toZeroLeOneClass

instance (priority := 100) CanonicallyOrderedAddMonoid.toZeroLeOneClass
    [CanonicallyOrderedAddMonoid α] [One α] : ZeroLEOneClass α :=
  ⟨zero_le 1⟩
#align canonically_ordered_add_monoid.to_zero_le_one_class CanonicallyOrderedAddMonoid.toZeroLeOneClass

namespace WithZero

instance preorder [Preorder α] : Preorder (WithZero α) :=
  WithBot.preorder

instance partialOrder [PartialOrder α] : PartialOrder (WithZero α) :=
  WithBot.partialOrder

instance orderBot [Preorder α] : OrderBot (WithZero α) :=
  WithBot.orderBot

theorem zero_le [Preorder α] (a : WithZero α) : 0 ≤ a :=
  bot_le
#align with_zero.zero_le WithZero.zero_le

theorem zero_lt_coe [Preorder α] (a : α) : (0 : WithZero α) < a :=
  WithBot.bot_lt_coe a
#align with_zero.zero_lt_coe WithZero.zero_lt_coe

theorem zero_eq_bot [Preorder α] : (0 : WithZero α) = ⊥ :=
  rfl
#align with_zero.zero_eq_bot WithZero.zero_eq_bot

@[simp, norm_cast]
theorem coe_lt_coe [Preorder α] {a b : α} : (a : WithZero α) < b ↔ a < b :=
  WithBot.coe_lt_coe
#align with_zero.coe_lt_coe WithZero.coe_lt_coe

@[simp, norm_cast]
theorem coe_le_coe [Preorder α] {a b : α} : (a : WithZero α) ≤ b ↔ a ≤ b :=
  WithBot.coe_le_coe
#align with_zero.coe_le_coe WithZero.coe_le_coe

instance lattice [Lattice α] : Lattice (WithZero α) :=
  WithBot.lattice

instance linearOrder [LinearOrder α] : LinearOrder (WithZero α) :=
  WithBot.linearOrder

instance covariantClass_mul_le [Mul α] [Preorder α]
    [CovariantClass α α (· * ·) (· ≤ ·)] :
    CovariantClass (WithZero α) (WithZero α) (· * ·) (· ≤ ·) := by
  refine ⟨fun a b c hbc => ?_⟩
  -- ⊢ a * b ≤ a * c
  induction a using WithZero.recZeroCoe; · exact zero_le _
  -- ⊢ 0 * b ≤ 0 * c
                                           -- 🎉 no goals
  induction b using WithZero.recZeroCoe; · exact zero_le _
  -- ⊢ ↑a✝ * 0 ≤ ↑a✝ * c
                                           -- 🎉 no goals
  rcases WithBot.coe_le_iff.1 hbc with ⟨c, rfl, hbc'⟩
  -- ⊢ ↑a✝¹ * ↑a✝ ≤ ↑a✝¹ * ↑c
  refine le_trans ?_ (le_of_eq <| coe_mul)
  -- ⊢ ↑a✝¹ * ↑a✝ ≤ ↑(a✝¹ * c)
  -- rw [← coe_mul, ← coe_mul, coe_le_coe]
  -- Porting note: rewriting `coe_mul` here doesn't work because of some difference between
  -- `coe` and `WithBot.some`, even though they're definitionally equal as shown by the `refine'`
  rw [← coe_mul, coe_le_coe]
  -- ⊢ a✝¹ * a✝ ≤ a✝¹ * c
  exact mul_le_mul_left' hbc' _
  -- 🎉 no goals
#align with_zero.covariant_class_mul_le WithZero.covariantClass_mul_le

-- Porting note: @[simp] can prove this
nonrec theorem le_max_iff [LinearOrder α] {a b c : α} :
    (a : WithZero α) ≤ max (b : WithZero α) c ↔ a ≤ max b c := by
  simp only [WithZero.coe_le_coe, le_max_iff]
  -- 🎉 no goals
#align with_zero.le_max_iff WithZero.le_max_iff

-- Porting note: @[simp] can prove this
nonrec theorem min_le_iff [LinearOrder α] {a b c : α} :
    min (a : WithZero α) b ≤ c ↔ min a b ≤ c := by
  simp only [WithZero.coe_le_coe, min_le_iff]
  -- 🎉 no goals
#align with_zero.min_le_iff WithZero.min_le_iff

instance orderedCommMonoid [OrderedCommMonoid α] : OrderedCommMonoid (WithZero α) :=
  { WithZero.commMonoidWithZero.toCommMonoid, WithZero.partialOrder with
    mul_le_mul_left := fun _ _ => mul_le_mul_left' }

-- FIXME: `WithOne.coe_mul` and `WithZero.coe_mul` have inconsistent use of implicit parameters

-- Porting note: same issue as `covariantClass_mul_le`
protected theorem covariantClass_add_le [AddZeroClass α] [Preorder α]
    [CovariantClass α α (· + ·) (· ≤ ·)] (h : ∀ a : α, 0 ≤ a) :
    CovariantClass (WithZero α) (WithZero α) (· + ·) (· ≤ ·) := by
  refine ⟨fun a b c hbc => ?_⟩
  -- ⊢ a + b ≤ a + c
  induction a using WithZero.recZeroCoe
  -- ⊢ 0 + b ≤ 0 + c
  · rwa [zero_add, zero_add]
    -- 🎉 no goals
  induction b using WithZero.recZeroCoe
  -- ⊢ ↑a✝ + 0 ≤ ↑a✝ + c
  · rw [add_zero]
    -- ⊢ ↑a✝ ≤ ↑a✝ + c
    induction c using WithZero.recZeroCoe
    -- ⊢ ↑a✝ ≤ ↑a✝ + 0
    · rw [add_zero]
      -- 🎉 no goals
    · rw [← coe_add, coe_le_coe]
      -- ⊢ a✝¹ ≤ a✝¹ + a✝
      exact le_add_of_nonneg_right (h _)
      -- 🎉 no goals
  · rcases WithBot.coe_le_iff.1 hbc with ⟨c, rfl, hbc'⟩
    -- ⊢ ↑a✝¹ + ↑a✝ ≤ ↑a✝¹ + ↑c
    refine le_trans ?_ (le_of_eq <| coe_add _ _)
    -- ⊢ ↑a✝¹ + ↑a✝ ≤ ↑(a✝¹ + c)
    rw [← coe_add, coe_le_coe]
    -- ⊢ a✝¹ + a✝ ≤ a✝¹ + c
    exact add_le_add_left hbc' _
    -- 🎉 no goals
#align with_zero.covariant_class_add_le WithZero.covariantClass_add_le

/-
Note 1 : the below is not an instance because it requires `zero_le`. It seems
like a rather pathological definition because α already has a zero.
Note 2 : there is no multiplicative analogue because it does not seem necessary.
Mathematicians might be more likely to use the order-dual version, where all
elements are ≤ 1 and then 1 is the top element.
-/
/-- If `0` is the least element in `α`, then `WithZero α` is an `OrderedAddCommMonoid`.
See note [reducible non-instances].
-/
@[reducible]
protected def orderedAddCommMonoid [OrderedAddCommMonoid α] (zero_le : ∀ a : α, 0 ≤ a) :
    OrderedAddCommMonoid (WithZero α) :=
  { WithZero.partialOrder, WithZero.addCommMonoid with
    add_le_add_left := @add_le_add_left _ _ _ (WithZero.covariantClass_add_le zero_le).. }
#align with_zero.ordered_add_comm_monoid WithZero.orderedAddCommMonoid

section CanonicallyOrderedMonoid

instance existsAddOfLE [Add α] [Preorder α] [ExistsAddOfLE α] :
    ExistsAddOfLE (WithZero α) :=
  ⟨fun {a b} => by
    induction a using WithZero.cases_on
    -- ⊢ 0 ≤ b → ∃ c, b = 0 + c
    · exact fun _ => ⟨b, (zero_add b).symm⟩
      -- 🎉 no goals
    induction b using WithZero.cases_on
    -- ⊢ ↑a✝ ≤ 0 → ∃ c, 0 = ↑a✝ + c
    · exact fun h => (WithBot.not_coe_le_bot _ h).elim
      -- 🎉 no goals
    intro h
    -- ⊢ ∃ c, ↑a✝ = ↑a✝¹ + c
    obtain ⟨c, rfl⟩ := exists_add_of_le (WithZero.coe_le_coe.1 h)
    -- ⊢ ∃ c_1, ↑(a✝ + c) = ↑a✝ + c_1
    exact ⟨c, rfl⟩⟩
    -- 🎉 no goals
#align with_zero.has_exists_add_of_le WithZero.existsAddOfLE

-- This instance looks absurd: a monoid already has a zero
/-- Adding a new zero to a canonically ordered additive monoid produces another one. -/
instance canonicallyOrderedAddMonoid [CanonicallyOrderedAddMonoid α] :
    CanonicallyOrderedAddMonoid (WithZero α) :=
  { WithZero.orderBot,
    WithZero.orderedAddCommMonoid _root_.zero_le,
    WithZero.existsAddOfLE with
    le_self_add := fun a b => by
      induction a using WithZero.cases_on
      -- ⊢ 0 ≤ 0 + b
      · exact bot_le
        -- 🎉 no goals
      induction b using WithZero.cases_on
      -- ⊢ ↑a✝ ≤ ↑a✝ + 0
      · exact le_rfl
        -- 🎉 no goals
      · exact WithZero.coe_le_coe.2 le_self_add }
        -- 🎉 no goals
#align with_zero.canonically_ordered_add_monoid WithZero.canonicallyOrderedAddMonoid

end CanonicallyOrderedMonoid

section CanonicallyLinearOrderedMonoid

instance canonicallyLinearOrderedAddMonoid (α : Type*)
    [CanonicallyLinearOrderedAddMonoid α] : CanonicallyLinearOrderedAddMonoid (WithZero α) :=
  { WithZero.canonicallyOrderedAddMonoid, WithZero.linearOrder with }
#align with_zero.canonically_linear_ordered_add_monoid WithZero.canonicallyLinearOrderedAddMonoid

end CanonicallyLinearOrderedMonoid

end WithZero
