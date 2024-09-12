/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot
-/
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Ring.Pi

/-!
# Pi instances for ordered groups and monoids

This file defines instances for ordered group, monoid, and related structures on Pi types.
-/

variable {ι I α β γ : Type*}

-- The indexing type
variable {f : I → Type*}

-- The family of types already equipped with instances
variable (x y : ∀ i, f i) (i : I)

namespace Pi

/-- The product of a family of ordered commutative monoids is an ordered commutative monoid. -/
@[to_additive
      "The product of a family of ordered additive commutative monoids is
an ordered additive commutative monoid."]
instance orderedCommMonoid {ι : Type*} {Z : ι → Type*} [∀ i, OrderedCommMonoid (Z i)] :
    OrderedCommMonoid (∀ i, Z i) where
  __ := Pi.partialOrder
  __ := Pi.commMonoid
  mul_le_mul_left _ _ w _ := fun i => mul_le_mul_left' (w i) _

@[to_additive]
instance existsMulOfLe {ι : Type*} {α : ι → Type*} [∀ i, LE (α i)] [∀ i, Mul (α i)]
    [∀ i, ExistsMulOfLE (α i)] : ExistsMulOfLE (∀ i, α i) :=
  ⟨fun h =>
    ⟨fun i => (exists_mul_of_le <| h i).choose,
      funext fun i => (exists_mul_of_le <| h i).choose_spec⟩⟩

/-- The product of a family of canonically ordered monoids is a canonically ordered monoid. -/
@[to_additive
      "The product of a family of canonically ordered additive monoids is
a canonically ordered additive monoid."]
instance {ι : Type*} {Z : ι → Type*} [∀ i, CanonicallyOrderedCommMonoid (Z i)] :
    CanonicallyOrderedCommMonoid (∀ i, Z i) where
  __ := Pi.instOrderBot
  __ := Pi.orderedCommMonoid
  __ := Pi.existsMulOfLe
  le_self_mul _ _ := fun _ => le_self_mul

@[to_additive]
instance orderedCancelCommMonoid [∀ i, OrderedCancelCommMonoid <| f i] :
    OrderedCancelCommMonoid (∀ i : I, f i) where
  __ := Pi.commMonoid
  le_of_mul_le_mul_left _ _ _ h i := le_of_mul_le_mul_left' (h i)
  mul_le_mul_left _ _ c h i := mul_le_mul_left' (c i) (h i)

@[to_additive]
instance orderedCommGroup [∀ i, OrderedCommGroup <| f i] : OrderedCommGroup (∀ i : I, f i) where
  __ := Pi.commGroup
  __ := Pi.orderedCommMonoid
  npow := Monoid.npow

instance orderedSemiring [∀ i, OrderedSemiring (f i)] : OrderedSemiring (∀ i, f i) where
  __ := Pi.semiring
  __ := Pi.partialOrder
  add_le_add_left _ _ hab _ := fun _ => add_le_add_left (hab _) _
  zero_le_one := fun i => zero_le_one (α := f i)
  mul_le_mul_of_nonneg_left _ _ _ hab hc := fun _ => mul_le_mul_of_nonneg_left (hab _) <| hc _
  mul_le_mul_of_nonneg_right _ _ _ hab hc := fun _ => mul_le_mul_of_nonneg_right (hab _) <| hc _

instance orderedCommSemiring [∀ i, OrderedCommSemiring (f i)] : OrderedCommSemiring (∀ i, f i) where
  __ := Pi.commSemiring
  __ := Pi.orderedSemiring

instance orderedRing [∀ i, OrderedRing (f i)] : OrderedRing (∀ i, f i) where
  __ := Pi.ring
  __ := Pi.orderedSemiring
  mul_nonneg _ _ ha hb := fun _ => mul_nonneg (ha _) (hb _)

instance orderedCommRing [∀ i, OrderedCommRing (f i)] : OrderedCommRing (∀ i, f i) where
  __ := Pi.commRing
  __ := Pi.orderedRing

end Pi

namespace Function
section const
variable (β) [One α] [Preorder α] {a : α}

@[to_additive const_nonneg_of_nonneg]
theorem one_le_const_of_one_le (ha : 1 ≤ a) : 1 ≤ const β a := fun _ => ha

@[to_additive]
theorem const_le_one_of_le_one (ha : a ≤ 1) : const β a ≤ 1 := fun _ => ha

variable {β} [Nonempty β]

@[to_additive (attr := simp) const_nonneg]
theorem one_le_const : 1 ≤ const β a ↔ 1 ≤ a :=
  const_le_const

@[to_additive (attr := simp) const_pos]
theorem one_lt_const : 1 < const β a ↔ 1 < a :=
  const_lt_const

@[to_additive (attr := simp)]
theorem const_le_one : const β a ≤ 1 ↔ a ≤ 1 :=
  const_le_const

@[to_additive (attr := simp) const_neg']
theorem const_lt_one : const β a < 1 ↔ a < 1 :=
  const_lt_const

end const

section extend
variable [One γ] [LE γ] {f : α → β} {g : α → γ} {e : β → γ}

@[to_additive extend_nonneg] lemma one_le_extend (hg : 1 ≤ g) (he : 1 ≤ e) : 1 ≤ extend f g e :=
  fun _b ↦ by classical exact one_le_dite (fun _ ↦ hg _) (fun _ ↦ he _)

@[to_additive] lemma extend_le_one (hg : g ≤ 1) (he : e ≤ 1) : extend f g e ≤ 1 :=
  fun _b ↦ by classical exact dite_le_one (fun _ ↦ hg _) (fun _ ↦ he _)

end extend
end Function
-- Porting note: Tactic code not ported yet
-- namespace Tactic

-- open Function

-- variable (ι) [Zero α] {a : α}

-- private theorem function_const_nonneg_of_pos [Preorder α] (ha : 0 < a) : 0 ≤ const ι a :=
--   const_nonneg_of_nonneg _ ha.le

-- variable [Nonempty ι]

-- private theorem function_const_ne_zero : a ≠ 0 → const ι a ≠ 0 :=
--   const_ne_zero.2

-- private theorem function_const_pos [Preorder α] : 0 < a → 0 < const ι a :=
--   const_pos.2

-- /-- Extension for the `positivity` tactic: `Function.const` is positive/nonnegative/nonzero if
-- its input is. -/
-- @[positivity]
-- unsafe def positivity_const : expr → tactic strictness
--   | q(Function.const $(ι) $(a)) => do
--     let strict_a ← core a
--     match strict_a with
--       | positive p =>
--         positive <$> to_expr ``(function_const_pos $(ι) $(p)) <|>
--           nonnegative <$> to_expr ``(function_const_nonneg_of_pos $(ι) $(p))
--       | nonnegative p => nonnegative <$> to_expr ``(const_nonneg_of_nonneg $(ι) $(p))
--       | nonzero p => nonzero <$> to_expr ``(function_const_ne_zero $(ι) $(p))
--   | e =>
--     pp e >>= fail ∘ format.bracket "The expression `" "` is not of the form `Function.const ι a`"

-- end Tactic
