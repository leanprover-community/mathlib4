/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Mathbin.Algebra.Group.WithOne.Defs
import Mathbin.Algebra.Order.Monoid.Canonical.Defs

/-!
# Adjoining a zero element to an ordered monoid.
-/


open Function

universe u

variable {α : Type u}

/-- Typeclass for expressing that the `0` of a type is less or equal to its `1`. -/
class ZeroLeOneClass (α : Type _) [Zero α] [One α] [LE α] where
  zero_le_one : (0 : α) ≤ 1
#align zero_le_one_class ZeroLeOneClass

/-- A linearly ordered commutative monoid with a zero element. -/
class LinearOrderedCommMonoidWithZero (α : Type _) extends LinearOrderedCommMonoid α,
  CommMonoidWithZero α where
  zero_le_one : (0 : α) ≤ 1
#align linear_ordered_comm_monoid_with_zero LinearOrderedCommMonoidWithZero

instance (priority := 100) LinearOrderedCommMonoidWithZero.toZeroLeOneClass
    [LinearOrderedCommMonoidWithZero α] : ZeroLeOneClass α :=
  { ‹LinearOrderedCommMonoidWithZero α› with }
#align
  linear_ordered_comm_monoid_with_zero.to_zero_le_one_class LinearOrderedCommMonoidWithZero.toZeroLeOneClass

instance (priority := 100) CanonicallyOrderedAddMonoid.toZeroLeOneClass
    [CanonicallyOrderedAddMonoid α] [One α] : ZeroLeOneClass α :=
  ⟨zero_le 1⟩
#align
  canonically_ordered_add_monoid.to_zero_le_one_class CanonicallyOrderedAddMonoid.toZeroLeOneClass

/-- `zero_le_one` with the type argument implicit. -/
@[simp]
theorem zero_le_one [Zero α] [One α] [LE α] [ZeroLeOneClass α] : (0 : α) ≤ 1 :=
  ZeroLeOneClass.zero_le_one
#align zero_le_one zero_le_one

/-- `zero_le_one` with the type argument explicit. -/
theorem zero_le_one' (α) [Zero α] [One α] [LE α] [ZeroLeOneClass α] : (0 : α) ≤ 1 :=
  zero_le_one
#align zero_le_one' zero_le_one'

theorem zero_le_two [Preorder α] [One α] [AddZeroClass α] [ZeroLeOneClass α]
    [CovariantClass α α (· + ·) (· ≤ ·)] : (0 : α) ≤ 2 :=
  add_nonneg zero_le_one zero_le_one
#align zero_le_two zero_le_two

theorem zero_le_three [Preorder α] [One α] [AddZeroClass α] [ZeroLeOneClass α]
    [CovariantClass α α (· + ·) (· ≤ ·)] : (0 : α) ≤ 3 :=
  add_nonneg zero_le_two zero_le_one
#align zero_le_three zero_le_three

theorem zero_le_four [Preorder α] [One α] [AddZeroClass α] [ZeroLeOneClass α]
    [CovariantClass α α (· + ·) (· ≤ ·)] : (0 : α) ≤ 4 :=
  add_nonneg zero_le_two zero_le_two
#align zero_le_four zero_le_four

theorem one_le_two [LE α] [One α] [AddZeroClass α] [ZeroLeOneClass α]
    [CovariantClass α α (· + ·) (· ≤ ·)] : (1 : α) ≤ 2 :=
  calc
    1 = 1 + 0 := (add_zero 1).symm
    _ ≤ 1 + 1 := add_le_add_left zero_le_one _
    
#align one_le_two one_le_two

theorem one_le_two' [LE α] [One α] [AddZeroClass α] [ZeroLeOneClass α]
    [CovariantClass α α (swap (· + ·)) (· ≤ ·)] : (1 : α) ≤ 2 :=
  calc
    1 = 0 + 1 := (zero_add 1).symm
    _ ≤ 1 + 1 := add_le_add_right zero_le_one _
    
#align one_le_two' one_le_two'

namespace WithZero

attribute [local semireducible] WithZero

instance [Preorder α] : Preorder (WithZero α) :=
  WithBot.preorder

instance [PartialOrder α] : PartialOrder (WithZero α) :=
  WithBot.partialOrder

instance [Preorder α] : OrderBot (WithZero α) :=
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

instance [Lattice α] : Lattice (WithZero α) :=
  WithBot.lattice

instance [LinearOrder α] : LinearOrder (WithZero α) :=
  WithBot.linearOrder

instance covariant_class_mul_le {α : Type u} [Mul α] [Preorder α]
    [CovariantClass α α (· * ·) (· ≤ ·)] :
    CovariantClass (WithZero α) (WithZero α) (· * ·) (· ≤ ·) := by
  refine' ⟨fun a b c hbc => _⟩
  induction a using WithZero.recZeroCoe; · exact zero_le _
  induction b using WithZero.recZeroCoe; · exact zero_le _
  rcases WithBot.coe_le_iff.1 hbc with ⟨c, rfl, hbc'⟩
  rw [← coe_mul, ← coe_mul, coe_le_coe]
  exact mul_le_mul_left' hbc' a
#align with_zero.covariant_class_mul_le WithZero.covariant_class_mul_le

@[simp]
theorem le_max_iff [LinearOrder α] {a b c : α} : (a : WithZero α) ≤ max b c ↔ a ≤ max b c := by
  simp only [WithZero.coe_le_coe, le_max_iff]
#align with_zero.le_max_iff WithZero.le_max_iff

@[simp]
theorem min_le_iff [LinearOrder α] {a b c : α} : min (a : WithZero α) b ≤ c ↔ min a b ≤ c := by
  simp only [WithZero.coe_le_coe, min_le_iff]
#align with_zero.min_le_iff WithZero.min_le_iff

instance [OrderedCommMonoid α] : OrderedCommMonoid (WithZero α) :=
  { WithZero.commMonoidWithZero, WithZero.partialOrder with
    mul_le_mul_left := fun _ _ => mul_le_mul_left' }

protected theorem covariant_class_add_le [AddZeroClass α] [Preorder α]
    [CovariantClass α α (· + ·) (· ≤ ·)] (h : ∀ a : α, 0 ≤ a) :
    CovariantClass (WithZero α) (WithZero α) (· + ·) (· ≤ ·) := by
  refine' ⟨fun a b c hbc => _⟩
  induction a using WithZero.recZeroCoe
  · rwa [zero_add, zero_add]
  induction b using WithZero.recZeroCoe
  · rw [add_zero]
    induction c using WithZero.recZeroCoe
    · rw [add_zero]
      exact le_rfl
    · rw [← coe_add, coe_le_coe]
      exact le_add_of_nonneg_right (h _)
  · rcases WithBot.coe_le_iff.1 hbc with ⟨c, rfl, hbc'⟩
    rw [← coe_add, ← coe_add, coe_le_coe]
    exact add_le_add_left hbc' a
#align with_zero.covariant_class_add_le WithZero.covariant_class_add_le

/-
Note 1 : the below is not an instance because it requires `zero_le`. It seems
like a rather pathological definition because α already has a zero.
Note 2 : there is no multiplicative analogue because it does not seem necessary.
Mathematicians might be more likely to use the order-dual version, where all
elements are ≤ 1 and then 1 is the top element.
-/
/-- If `0` is the least element in `α`, then `with_zero α` is an `ordered_add_comm_monoid`.
See note [reducible non-instances].
-/
@[reducible]
protected def orderedAddCommMonoid [OrderedAddCommMonoid α] (zero_le : ∀ a : α, 0 ≤ a) :
    OrderedAddCommMonoid (WithZero α) :=
  { WithZero.partialOrder, WithZero.addCommMonoid with
    add_le_add_left := @add_le_add_left _ _ _ (WithZero.covariant_class_add_le zero_le).. }
#align with_zero.ordered_add_comm_monoid WithZero.orderedAddCommMonoid

end WithZero

section CanonicallyOrderedMonoid

instance WithZero.has_exists_add_of_le {α} [Add α] [Preorder α] [HasExistsAddOfLe α] :
    HasExistsAddOfLe (WithZero α) :=
  ⟨fun a b => by 
    apply WithZero.cases_on a
    · exact fun _ => ⟨b, (zero_add b).symm⟩
    apply WithZero.cases_on b
    · exact fun b' h => (WithBot.not_coe_le_bot _ h).elim
    rintro a' b' h
    obtain ⟨c, rfl⟩ := exists_add_of_le (WithZero.coe_le_coe.1 h)
    exact ⟨c, rfl⟩⟩
#align with_zero.has_exists_add_of_le WithZero.has_exists_add_of_le

-- This instance looks absurd: a monoid already has a zero
/-- Adding a new zero to a canonically ordered additive monoid produces another one. -/
instance WithZero.canonicallyOrderedAddMonoid {α : Type u} [CanonicallyOrderedAddMonoid α] :
    CanonicallyOrderedAddMonoid (WithZero α) :=
  { WithZero.orderBot, WithZero.orderedAddCommMonoid zero_le, WithZero.has_exists_add_of_le with
    le_self_add := fun a b => by 
      apply WithZero.cases_on a
      · exact bot_le
      apply WithZero.cases_on b
      · exact fun b' => le_rfl
      · exact fun a' b' => WithZero.coe_le_coe.2 le_self_add }
#align with_zero.canonically_ordered_add_monoid WithZero.canonicallyOrderedAddMonoid

end CanonicallyOrderedMonoid

section CanonicallyLinearOrderedMonoid

instance WithZero.canonicallyLinearOrderedAddMonoid (α : Type _)
    [CanonicallyLinearOrderedAddMonoid α] : CanonicallyLinearOrderedAddMonoid (WithZero α) :=
  { WithZero.canonicallyOrderedAddMonoid, WithZero.linearOrder with }
#align with_zero.canonically_linear_ordered_add_monoid WithZero.canonicallyLinearOrderedAddMonoid

end CanonicallyLinearOrderedMonoid

