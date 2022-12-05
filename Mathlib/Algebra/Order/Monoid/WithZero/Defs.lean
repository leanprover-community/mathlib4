/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Mathlib.Algebra.Group.WithOne.Defs
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Tactic.NormNum

/-!
# Adjoining a zero element to an ordered monoid.
-/


open Function

universe u

variable {α : Type u}

/-- Typeclass for expressing that the `0` of a type is less or equal to its `1`. -/
class ZeroLEOneClass (α : Type _) [Zero α] [One α] [LE α] where
  zero_le_one : (0 : α) ≤ 1
#align zero_le_one_class ZeroLEOneClass

/-- A linearly ordered commutative monoid with a zero element. -/
class LinearOrderedCommMonoidWithZero (α : Type _) extends LinearOrderedCommMonoid α,
  CommMonoidWithZero α where
  zero_le_one : (0 : α) ≤ 1
#align linear_ordered_comm_monoid_with_zero LinearOrderedCommMonoidWithZero

instance (priority := 100) LinearOrderedCommMonoidWithZero.toZeroLEOneClass
    [LinearOrderedCommMonoidWithZero α] : ZeroLEOneClass α :=
  { ‹LinearOrderedCommMonoidWithZero α› with }
#align
  linear_ordered_comm_monoid_with_zero.to_zero_le_one_class
  LinearOrderedCommMonoidWithZero.toZeroLEOneClass

instance (priority := 100) CanonicallyOrderedAddMonoid.toZeroLEOneClass
    [CanonicallyOrderedAddMonoid α] [One α] : ZeroLEOneClass α :=
  ⟨zero_le 1⟩
#align
  canonically_ordered_add_monoid.to_zero_le_one_class
  CanonicallyOrderedAddMonoid.toZeroLEOneClass

/-- `zero_le_one` with the type argument implicit. -/
@[simp]
theorem zero_le_one [Zero α] [One α] [LE α] [ZeroLEOneClass α] : (0 : α) ≤ 1 :=
  ZeroLEOneClass.zero_le_one
#align zero_le_one zero_le_one

/-- `zero_le_one` with the type argument explicit. -/
theorem zero_le_one' (α) [Zero α] [One α] [LE α] [ZeroLEOneClass α] : (0 : α) ≤ 1 :=
  zero_le_one
#align zero_le_one' zero_le_one'

-- Porting note: In the following lemmas, we now assume that we have an `AddMonoidWithOne`
-- instance for `α`. Note that mathlib3#17820 may move these lemmas into another file.
-- We also now import `norm_num` to normalise things like `2 + 2 = 4`.

theorem zero_le_two [Preorder α] [AddMonoidWithOne α] [ZeroLEOneClass α]
    [CovariantClass α α (· + ·) (· ≤ ·)] : (0 : α) ≤ 2 :=
  le_of_le_of_eq (add_nonneg zero_le_one zero_le_one) one_add_one_eq_two
#align zero_le_two zero_le_two

theorem zero_le_three [Preorder α] [AddMonoidWithOne α] [ZeroLEOneClass α]
    [CovariantClass α α (· + ·) (· ≤ ·)] : (0 : α) ≤ 3 := by
  refine le_of_le_of_eq (add_nonneg zero_le_two zero_le_one) ?_
  norm_num
#align zero_le_three zero_le_three

theorem zero_le_four [Preorder α] [AddMonoidWithOne α] [ZeroLEOneClass α]
    [CovariantClass α α (· + ·) (· ≤ ·)] : (0 : α) ≤ 4 := by
  refine le_of_le_of_eq (add_nonneg zero_le_two zero_le_two) ?_
  norm_num
#align zero_le_four zero_le_four

theorem one_le_two [Preorder α] [AddMonoidWithOne α] [ZeroLEOneClass α]
    [CovariantClass α α (· + ·) (· ≤ ·)] : (1 : α) ≤ 2 :=
  calc
    1 = 1 + 0 := (add_zero 1).symm
    _ ≤ 1 + 1 := add_le_add_left zero_le_one _
    _ = 2 := by norm_num
#align one_le_two one_le_two

theorem one_le_two' [LE α] [AddMonoidWithOne α] [ZeroLEOneClass α]
    [CovariantClass α α (swap (· + ·)) (· ≤ ·)] : (1 : α) ≤ 2 :=
  calc
    1 = 0 + 1 := (zero_add 1).symm
    _ ≤ 1 + 1 := add_le_add_right zero_le_one _
    _ = 2 := by norm_num
#align one_le_two' one_le_two'

namespace WithZero

instance [Preorder α] : Preorder (WithZero α) :=
  WithBot.instPreorderWithBot

instance [PartialOrder α] : PartialOrder (WithZero α) :=
  WithBot.instPartialOrderWithBot

instance [Preorder α] : OrderBot (WithZero α) :=
  WithBot.instOrderBotWithBotInstLEWithBot

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
  WithBot.instLatticeWithBot

instance [LinearOrder α] : LinearOrder (WithZero α) :=
  WithBot.instLinearOrderWithBot

instance covariantClass_mul_le [Mul α] [Preorder α]
    [CovariantClass α α (· * ·) (· ≤ ·)] :
    CovariantClass (WithZero α) (WithZero α) (· * ·) (· ≤ ·) := by
  refine ⟨fun a b c hbc => ?_⟩
  induction a using WithZero.recZeroCoe; · exact zero_le _
  induction b using WithZero.recZeroCoe; · exact zero_le _
  rcases WithBot.coe_le_iff.1 hbc with ⟨c, rfl, hbc'⟩
  refine le_trans ?_ (le_of_eq <| coe_mul)
  -- rw [← coe_mul, ← coe_mul, coe_le_coe]
  -- Porting note: rewriting `coe_mul` here doesn't work because of some difference between
  -- `coe` and `WithBot.some`, even though they're definitionally equal as shown by the `refine'`
  rw [← coe_mul, coe_le_coe]
  exact mul_le_mul_left' hbc' _
#align with_zero.covariant_class_mul_le WithZero.covariantClass_mul_le

@[simp]
theorem le_max_iff [LinearOrder α] {a b c : α} : (a : WithZero α) ≤ max b c ↔ a ≤ max b c := by
  simp only [WithZero.coe_le_coe, le_max_iff]
  rfl
#align with_zero.le_max_iff WithZero.le_max_iff

-- Porting note: `_root_` was needed here, but not in the previous lemma
@[simp]
theorem min_le_iff [LinearOrder α] {a b c : α} : min (a : WithZero α) b ≤ c ↔ min a b ≤ c := by
  simp only [WithZero.coe_le_coe, _root_.min_le_iff]
  rfl
#align with_zero.min_le_iff WithZero.min_le_iff

instance [OrderedCommMonoid α] : OrderedCommMonoid (WithZero α) :=
  { CommMonoidWithZero.toCommMonoid, WithZero.instPartialOrderWithZero with
    mul_le_mul_left := fun _ _ => mul_le_mul_left' }

-- FIXME: `WithOne.coe_mul` and `WithZero.coe_mul` have inconsistent use of implicit parameters

-- Porting note: same issue as `covariantClass_mul_le`
protected theorem covariantClass_add_le [AddZeroClass α] [Preorder α]
    [CovariantClass α α (· + ·) (· ≤ ·)] (h : ∀ a : α, 0 ≤ a) :
    CovariantClass (WithZero α) (WithZero α) (· + ·) (· ≤ ·) := by
  refine ⟨fun a b c hbc => ?_⟩
  induction a using WithZero.recZeroCoe
  · rwa [zero_add, zero_add]
  induction b using WithZero.recZeroCoe
  · rw [add_zero]
    induction c using WithZero.recZeroCoe
    · rw [add_zero]
    · rw [← coe_add, coe_le_coe]
      exact le_add_of_nonneg_right (h _)
  · rcases WithBot.coe_le_iff.1 hbc with ⟨c, rfl, hbc'⟩
    refine le_trans ?_ (le_of_eq <| coe_add _ _)
    rw [← coe_add, coe_le_coe]
    exact add_le_add_left hbc' _
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
  { WithZero.instPartialOrderWithZero, instAddCommMonoidWithZero with
    add_le_add_left := @add_le_add_left _ _ _ (WithZero.covariantClass_add_le zero_le).. }
#align with_zero.ordered_add_comm_monoid WithZero.orderedAddCommMonoid

end WithZero

section CanonicallyOrderedMonoid

instance WithZero.instExistsAddOfLE [Add α] [Preorder α] [ExistsAddOfLE α] :
    ExistsAddOfLE (WithZero α) :=
  ⟨fun {a b} => by
    apply WithZero.cases_on a
    · exact fun _ => ⟨b, (zero_add b).symm⟩
    apply WithZero.cases_on b
    · exact fun b' h => (WithBot.not_coe_le_bot _ h).elim
    rintro a' b' h
    obtain ⟨c, rfl⟩ := exists_add_of_le (WithZero.coe_le_coe.1 h)
    exact ⟨c, rfl⟩⟩
#align with_zero.has_exists_add_of_le WithZero.instExistsAddOfLE

-- This instance looks absurd: a monoid already has a zero
/-- Adding a new zero to a canonically ordered additive monoid produces another one. -/
instance WithZero.canonicallyOrderedAddMonoid [CanonicallyOrderedAddMonoid α] :
    CanonicallyOrderedAddMonoid (WithZero α) :=
  { WithZero.instOrderBotWithZeroToLEInstPreorderWithZero,
    WithZero.orderedAddCommMonoid _root_.zero_le,
    WithZero.instExistsAddOfLE with
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
  { WithZero.canonicallyOrderedAddMonoid, WithZero.instLinearOrderWithZero with }
#align with_zero.canonically_linear_ordered_add_monoid WithZero.canonicallyLinearOrderedAddMonoid

end CanonicallyLinearOrderedMonoid
