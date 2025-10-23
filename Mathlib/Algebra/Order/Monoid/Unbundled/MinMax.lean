/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic

/-!
# Lemmas about `min` and `max` in an ordered monoid.
-/


open Function

variable {α β : Type*}

/-! Some lemmas about types that have an ordering and a binary operation, with no
  rules relating them. -/

section CommSemigroup
variable [LinearOrder α] [CommSemigroup β]

@[to_additive]
lemma fn_min_mul_fn_max (f : α → β) (a b : α) : f (min a b) * f (max a b) = f a * f b := by
  grind

@[to_additive]
lemma fn_max_mul_fn_min (f : α → β) (a b : α) : f (max a b) * f (min a b) = f a * f b := by
  grind

variable [CommSemigroup α]

@[to_additive (attr := simp)]
lemma min_mul_max (a b : α) : min a b * max a b = a * b := fn_min_mul_fn_max id _ _

@[to_additive (attr := simp)]
lemma max_mul_min (a b : α) : max a b * min a b = a * b := fn_max_mul_fn_min id _ _

end CommSemigroup

section CovariantClassMulLe

variable [LinearOrder α]

section Mul

variable [Mul α]

section Left

variable [MulLeftMono α]

@[to_additive]
theorem min_mul_mul_left (a b c : α) : min (a * b) (a * c) = a * min b c :=
  (monotone_id.const_mul' a).map_min.symm

@[to_additive]
theorem max_mul_mul_left (a b c : α) : max (a * b) (a * c) = a * max b c :=
  (monotone_id.const_mul' a).map_max.symm

end Left

section Right

variable [MulRightMono α]

@[to_additive]
theorem min_mul_mul_right (a b c : α) : min (a * c) (b * c) = min a b * c :=
  (monotone_id.mul_const' c).map_min.symm

@[to_additive]
theorem max_mul_mul_right (a b c : α) : max (a * c) (b * c) = max a b * c :=
  (monotone_id.mul_const' c).map_max.symm

end Right

@[to_additive]
theorem lt_or_lt_of_mul_lt_mul [MulLeftMono α] [MulRightMono α] {a₁ a₂ b₁ b₂ : α} :
    a₁ * b₁ < a₂ * b₂ → a₁ < a₂ ∨ b₁ < b₂ := by
  contrapose!
  exact fun h => mul_le_mul' h.1 h.2

@[to_additive]
theorem le_or_lt_of_mul_le_mul [MulLeftMono α] [MulRightStrictMono α] {a₁ a₂ b₁ b₂ : α} :
    a₁ * b₁ ≤ a₂ * b₂ → a₁ ≤ a₂ ∨ b₁ < b₂ := by
  contrapose!
  exact fun h => mul_lt_mul_of_lt_of_le h.1 h.2

@[to_additive]
theorem lt_or_le_of_mul_le_mul [MulLeftStrictMono α] [MulRightMono α] {a₁ a₂ b₁ b₂ : α} :
    a₁ * b₁ ≤ a₂ * b₂ → a₁ < a₂ ∨ b₁ ≤ b₂ := by
  contrapose!
  exact fun h => mul_lt_mul_of_le_of_lt h.1 h.2

@[to_additive]
theorem le_or_le_of_mul_le_mul [MulLeftStrictMono α] [MulRightStrictMono α] {a₁ a₂ b₁ b₂ : α} :
    a₁ * b₁ ≤ a₂ * b₂ → a₁ ≤ a₂ ∨ b₁ ≤ b₂ := by
  contrapose!
  exact fun h => mul_lt_mul_of_lt_of_lt h.1 h.2

@[to_additive]
theorem mul_lt_mul_iff_of_le_of_le [MulLeftMono α]
    [MulRightMono α] [MulLeftStrictMono α]
    [MulRightStrictMono α] {a₁ a₂ b₁ b₂ : α} (ha : a₁ ≤ a₂)
    (hb : b₁ ≤ b₂) : a₁ * b₁ < a₂ * b₂ ↔ a₁ < a₂ ∨ b₁ < b₂ := by
  refine ⟨lt_or_lt_of_mul_lt_mul, fun h => ?_⟩
  rcases h with ha' | hb'
  · exact mul_lt_mul_of_lt_of_le ha' hb
  · exact mul_lt_mul_of_le_of_lt ha hb'

end Mul

variable [MulOneClass α]

@[to_additive]
theorem min_le_mul_of_one_le_right [MulLeftMono α] {a b : α} (hb : 1 ≤ b) :
    min a b ≤ a * b :=
  min_le_iff.2 <| Or.inl <| le_mul_of_one_le_right' hb

@[to_additive]
theorem min_le_mul_of_one_le_left [MulRightMono α] {a b : α} (ha : 1 ≤ a) :
    min a b ≤ a * b :=
  min_le_iff.2 <| Or.inr <| le_mul_of_one_le_left' ha

@[to_additive]
theorem max_le_mul_of_one_le [MulLeftMono α] [MulRightMono α] {a b : α} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    max a b ≤ a * b :=
  max_le_iff.2 ⟨le_mul_of_one_le_right' hb, le_mul_of_one_le_left' ha⟩

end CovariantClassMulLe
