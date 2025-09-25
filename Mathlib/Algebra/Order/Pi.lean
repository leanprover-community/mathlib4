/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot
-/
import Mathlib.Algebra.Notation.Lemmas
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Ring.Pi

/-!
# Pi instances for ordered groups and monoids

This file defines instances for ordered group, monoid, and related structures on Pi types.
-/

variable {I α β γ : Type*}

-- The indexing type
variable {f : I → Type*}

namespace Pi

/-- The product of a family of ordered commutative monoids is an ordered commutative monoid. -/
@[to_additive
      /-- The product of a family of ordered additive commutative monoids is
an ordered additive commutative monoid. -/]
instance isOrderedMonoid {ι : Type*} {Z : ι → Type*} [∀ i, CommMonoid (Z i)]
    [∀ i, PartialOrder (Z i)] [∀ i, IsOrderedMonoid (Z i)] :
    IsOrderedMonoid (∀ i, Z i) where
  mul_le_mul_left _ _ w _ := fun i => mul_le_mul_left' (w i) _

@[to_additive]
instance existsMulOfLe {ι : Type*} {α : ι → Type*} [∀ i, LE (α i)] [∀ i, Mul (α i)]
    [∀ i, ExistsMulOfLE (α i)] : ExistsMulOfLE (∀ i, α i) :=
  ⟨fun h =>
    ⟨fun i => (exists_mul_of_le <| h i).choose,
      funext fun i => (exists_mul_of_le <| h i).choose_spec⟩⟩

/-- The product of a family of canonically ordered monoids is a canonically ordered monoid. -/
@[to_additive
      /-- The product of a family of canonically ordered additive monoids is
a canonically ordered additive monoid. -/]
instance {ι : Type*} {Z : ι → Type*} [∀ i, Monoid (Z i)] [∀ i, PartialOrder (Z i)]
    [∀ i, CanonicallyOrderedMul (Z i)] :
    CanonicallyOrderedMul (∀ i, Z i) where
  __ := Pi.existsMulOfLe
  le_mul_self _ _ := fun _ => le_mul_self
  le_self_mul _ _ := fun _ => le_self_mul

@[to_additive]
instance isOrderedCancelMonoid [∀ i, CommMonoid <| f i] [∀ i, PartialOrder <| f i]
    [∀ i, IsOrderedCancelMonoid <| f i] :
    IsOrderedCancelMonoid (∀ i : I, f i) where
  le_of_mul_le_mul_left _ _ _ h i := le_of_mul_le_mul_left' (h i)

instance isOrderedRing [∀ i, Semiring (f i)] [∀ i, PartialOrder (f i)] [∀ i, IsOrderedRing (f i)] :
    IsOrderedRing (∀ i, f i) where
  add_le_add_left _ _ hab _ := fun _ => add_le_add_left (hab _) _
  zero_le_one := fun i => zero_le_one (α := f i)
  mul_le_mul_of_nonneg_left _ _ _ hab hc := fun _ => mul_le_mul_of_nonneg_left (hab _) <| hc _
  mul_le_mul_of_nonneg_right _ _ _ hab hc := fun _ => mul_le_mul_of_nonneg_right (hab _) <| hc _

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

namespace Pi
variable {ι : Type*} {α : ι → Type*} [DecidableEq ι] [∀ i, One (α i)] [∀ i, Preorder (α i)] {i : ι}
  {a b : α i}

@[to_additive (attr := simp)]
lemma mulSingle_le_mulSingle : mulSingle i a ≤ mulSingle i b ↔ a ≤ b := by
  simp [mulSingle]

@[to_additive (attr := gcongr)] alias ⟨_, GCongr.mulSingle_mono⟩ := mulSingle_le_mulSingle

@[to_additive (attr := simp) single_nonneg]
lemma one_le_mulSingle : 1 ≤ mulSingle i a ↔ 1 ≤ a := by simp [mulSingle]

@[to_additive (attr := simp)]
lemma mulSingle_le_one : mulSingle i a ≤ 1 ↔ a ≤ 1 := by simp [mulSingle]

end Pi

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
