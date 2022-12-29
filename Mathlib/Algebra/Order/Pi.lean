/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot

! This file was ported from Lean 3 source module algebra.order.pi
! leanprover-community/mathlib commit 422e70f7ce183d2900c586a8cda8381e788a0c62
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Order.Ring.Defs
import Mathbin.Algebra.Ring.Pi
import Mathbin.Tactic.Positivity

/-!
# Pi instances for ordered groups and monoids

This file defines instances for ordered group, monoid, and related structures on Pi types.
-/


universe u v w

variable {ι α β : Type _}

variable {I : Type u}

-- The indexing type
variable {f : I → Type v}

-- The family of types already equipped with instances
variable (x y : ∀ i, f i) (i : I)

namespace Pi

/-- The product of a family of ordered commutative monoids is an ordered commutative monoid. -/
@[to_additive
      "The product of a family of ordered additive commutative monoids is\n  an ordered additive commutative monoid."]
instance orderedCommMonoid {ι : Type _} {Z : ι → Type _} [∀ i, OrderedCommMonoid (Z i)] :
    OrderedCommMonoid (∀ i, Z i) :=
  { Pi.partialOrder, Pi.commMonoid with
    mul_le_mul_left := fun f g w h i => mul_le_mul_left' (w i) _ }
#align pi.ordered_comm_monoid Pi.orderedCommMonoid

@[to_additive]
instance {ι : Type _} {α : ι → Type _} [∀ i, LE (α i)] [∀ i, Mul (α i)] [∀ i, ExistsMulOfLE (α i)] :
    ExistsMulOfLE (∀ i, α i) :=
  ⟨fun a b h =>
    ⟨fun i => (exists_mul_of_le <| h i).some, funext fun i => (exists_mul_of_le <| h i).some_spec⟩⟩

/-- The product of a family of canonically ordered monoids is a canonically ordered monoid. -/
@[to_additive
      "The product of a family of canonically ordered additive monoids is\n  a canonically ordered additive monoid."]
instance {ι : Type _} {Z : ι → Type _} [∀ i, CanonicallyOrderedMonoid (Z i)] :
    CanonicallyOrderedMonoid (∀ i, Z i) :=
  { Pi.orderBot, Pi.orderedCommMonoid, Pi.has_exists_mul_of_le with
    le_self_mul := fun f g i => le_self_mul }

@[to_additive]
instance orderedCancelCommMonoid [∀ i, OrderedCancelCommMonoid <| f i] :
    OrderedCancelCommMonoid (∀ i : I, f i) := by
  refine_struct
      { Pi.partialOrder, Pi.monoid with
        mul := (· * ·)
        one := (1 : ∀ i, f i)
        le := (· ≤ ·)
        lt := (· < ·)
        npow := Monoid.npow } <;>
    pi_instance_derive_field
#align pi.ordered_cancel_comm_monoid Pi.orderedCancelCommMonoid

@[to_additive]
instance orderedCommGroup [∀ i, OrderedCommGroup <| f i] : OrderedCommGroup (∀ i : I, f i) :=
  { Pi.commGroup, Pi.orderedCommMonoid with
    mul := (· * ·)
    one := (1 : ∀ i, f i)
    le := (· ≤ ·)
    lt := (· < ·)
    npow := Monoid.npow }
#align pi.ordered_comm_group Pi.orderedCommGroup

instance [∀ i, OrderedSemiring (f i)] : OrderedSemiring (∀ i, f i) :=
  { Pi.semiring,
    Pi.partialOrder with
    add_le_add_left := fun a b hab c i => add_le_add_left (hab _) _
    zero_le_one := fun _ => zero_le_one
    mul_le_mul_of_nonneg_left := fun a b c hab hc i => mul_le_mul_of_nonneg_left (hab _) <| hc _
    mul_le_mul_of_nonneg_right := fun a b c hab hc i => mul_le_mul_of_nonneg_right (hab _) <| hc _ }

instance [∀ i, OrderedCommSemiring (f i)] : OrderedCommSemiring (∀ i, f i) :=
  { Pi.commSemiring, Pi.orderedSemiring with }

instance [∀ i, OrderedRing (f i)] : OrderedRing (∀ i, f i) :=
  { Pi.ring, Pi.orderedSemiring with mul_nonneg := fun a b ha hb i => mul_nonneg (ha _) (hb _) }

instance [∀ i, OrderedCommRing (f i)] : OrderedCommRing (∀ i, f i) :=
  { Pi.commRing, Pi.orderedRing with }

end Pi

namespace Function

variable (β) [One α] [Preorder α] {a : α}

@[to_additive const_nonneg_of_nonneg]
theorem one_le_const_of_one_le (ha : 1 ≤ a) : 1 ≤ const β a := fun _ => ha
#align function.one_le_const_of_one_le Function.one_le_const_of_one_le

@[to_additive]
theorem const_le_one_of_le_one (ha : a ≤ 1) : const β a ≤ 1 := fun _ => ha
#align function.const_le_one_of_le_one Function.const_le_one_of_le_one

variable {β} [Nonempty β]

@[simp, to_additive const_nonneg]
theorem one_le_const : 1 ≤ const β a ↔ 1 ≤ a :=
  @const_le_const _ _ _ _ 1 _
#align function.one_le_const Function.one_le_const

@[simp, to_additive const_pos]
theorem one_lt_const : 1 < const β a ↔ 1 < a :=
  @const_lt_const _ _ _ _ 1 a
#align function.one_lt_const Function.one_lt_const

@[simp, to_additive]
theorem const_le_one : const β a ≤ 1 ↔ a ≤ 1 :=
  @const_le_const _ _ _ _ _ 1
#align function.const_le_one Function.const_le_one

@[simp, to_additive]
theorem const_lt_one : const β a < 1 ↔ a < 1 :=
  @const_lt_const _ _ _ _ _ 1
#align function.const_lt_one Function.const_lt_one

end Function

namespace Tactic

open Function Positivity

variable (ι) [Zero α] {a : α}

private theorem function_const_nonneg_of_pos [Preorder α] (ha : 0 < a) : 0 ≤ const ι a :=
  const_nonneg_of_nonneg _ ha.le
#align tactic.function_const_nonneg_of_pos tactic.function_const_nonneg_of_pos

variable [Nonempty ι]

private theorem function_const_ne_zero : a ≠ 0 → const ι a ≠ 0 :=
  const_ne_zero.2
#align tactic.function_const_ne_zero tactic.function_const_ne_zero

private theorem function_const_pos [Preorder α] : 0 < a → 0 < const ι a :=
  const_pos.2
#align tactic.function_const_pos tactic.function_const_pos

/-- Extension for the `positivity` tactic: `function.const` is positive/nonnegative/nonzero if its
input is. -/
@[positivity]
unsafe def positivity_const : expr → tactic strictness
  | q(Function.const $(ι) $(a)) => do
    let strict_a ← core a
    match strict_a with
      | positive p =>
        positive <$> to_expr ``(function_const_pos $(ι) $(p)) <|>
          nonnegative <$> to_expr ``(function_const_nonneg_of_pos $(ι) $(p))
      | nonnegative p => nonnegative <$> to_expr ``(const_nonneg_of_nonneg $(ι) $(p))
      | nonzero p => nonzero <$> to_expr ``(function_const_ne_zero $(ι) $(p))
  | e =>
    pp e >>= fail ∘ format.bracket "The expression `" "` is not of the form `function.const ι a`"
#align tactic.positivity_const tactic.positivity_const

end Tactic
