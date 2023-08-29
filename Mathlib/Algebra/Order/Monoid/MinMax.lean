/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Mathlib.Order.MinMax
import Mathlib.Algebra.Order.Monoid.Lemmas

#align_import algebra.order.monoid.min_max from "leanprover-community/mathlib"@"de87d5053a9fe5cbde723172c0fb7e27e7436473"

/-!
# Lemmas about `min` and `max` in an ordered monoid.
-/


open Function

variable {α β : Type*}

/-! Some lemmas about types that have an ordering and a binary operation, with no
  rules relating them. -/


@[to_additive]
theorem fn_min_mul_fn_max [LinearOrder α] [CommSemigroup β] (f : α → β) (n m : α) :
    f (min n m) * f (max n m) = f n * f m := by cases' le_total n m with h h <;> simp [h, mul_comm]
                                                -- ⊢ f (min n m) * f (max n m) = f n * f m
                                                                                 -- 🎉 no goals
                                                                                 -- 🎉 no goals
#align fn_min_mul_fn_max fn_min_mul_fn_max
#align fn_min_add_fn_max fn_min_add_fn_max

@[to_additive]
theorem min_mul_max [LinearOrder α] [CommSemigroup α] (n m : α) : min n m * max n m = n * m :=
  fn_min_mul_fn_max id n m
#align min_mul_max min_mul_max
#align min_add_max min_add_max

section CovariantClassMulLe

variable [LinearOrder α]

section Mul

variable [Mul α]

section Left

variable [CovariantClass α α (· * ·) (· ≤ ·)]

@[to_additive]
theorem min_mul_mul_left (a b c : α) : min (a * b) (a * c) = a * min b c :=
  (monotone_id.const_mul' a).map_min.symm
#align min_mul_mul_left min_mul_mul_left
#align min_add_add_left min_add_add_left

@[to_additive]
theorem max_mul_mul_left (a b c : α) : max (a * b) (a * c) = a * max b c :=
  (monotone_id.const_mul' a).map_max.symm
#align max_mul_mul_left max_mul_mul_left
#align max_add_add_left max_add_add_left

end Left

section Right

variable [CovariantClass α α (Function.swap (· * ·)) (· ≤ ·)]

@[to_additive]
theorem min_mul_mul_right (a b c : α) : min (a * c) (b * c) = min a b * c :=
  (monotone_id.mul_const' c).map_min.symm
#align min_mul_mul_right min_mul_mul_right
#align min_add_add_right min_add_add_right

@[to_additive]
theorem max_mul_mul_right (a b c : α) : max (a * c) (b * c) = max a b * c :=
  (monotone_id.mul_const' c).map_max.symm
#align max_mul_mul_right max_mul_mul_right
#align max_add_add_right max_add_add_right

end Right

@[to_additive]
theorem lt_or_lt_of_mul_lt_mul [CovariantClass α α (· * ·) (· ≤ ·)]
    [CovariantClass α α (Function.swap (· * ·)) (· ≤ ·)] {a₁ a₂ b₁ b₂ : α} :
    a₁ * b₁ < a₂ * b₂ → a₁ < a₂ ∨ b₁ < b₂ := by
  contrapose!
  -- ⊢ a₂ ≤ a₁ ∧ b₂ ≤ b₁ → a₂ * b₂ ≤ a₁ * b₁
  exact fun h => mul_le_mul' h.1 h.2
  -- 🎉 no goals
#align lt_or_lt_of_mul_lt_mul lt_or_lt_of_mul_lt_mul
#align lt_or_lt_of_add_lt_add lt_or_lt_of_add_lt_add

@[to_additive]
theorem le_or_lt_of_mul_le_mul [CovariantClass α α (· * ·) (· ≤ ·)]
    [CovariantClass α α (Function.swap (· * ·)) (· < ·)] {a₁ a₂ b₁ b₂ : α} :
    a₁ * b₁ ≤ a₂ * b₂ → a₁ ≤ a₂ ∨ b₁ < b₂ := by
  contrapose!
  -- ⊢ a₂ < a₁ ∧ b₂ ≤ b₁ → a₂ * b₂ < a₁ * b₁
  exact fun h => mul_lt_mul_of_lt_of_le h.1 h.2
  -- 🎉 no goals
#align le_or_lt_of_mul_le_mul le_or_lt_of_mul_le_mul
#align le_or_lt_of_add_le_add le_or_lt_of_add_le_add

@[to_additive]
theorem lt_or_le_of_mul_le_mul [CovariantClass α α (· * ·) (· < ·)]
    [CovariantClass α α (Function.swap (· * ·)) (· ≤ ·)] {a₁ a₂ b₁ b₂ : α} :
    a₁ * b₁ ≤ a₂ * b₂ → a₁ < a₂ ∨ b₁ ≤ b₂ := by
  contrapose!
  -- ⊢ a₂ ≤ a₁ ∧ b₂ < b₁ → a₂ * b₂ < a₁ * b₁
  exact fun h => mul_lt_mul_of_le_of_lt h.1 h.2
  -- 🎉 no goals
#align lt_or_le_of_mul_le_mul lt_or_le_of_mul_le_mul
#align lt_or_le_of_add_le_add lt_or_le_of_add_le_add

@[to_additive]
theorem le_or_le_of_mul_le_mul [CovariantClass α α (· * ·) (· < ·)]
    [CovariantClass α α (Function.swap (· * ·)) (· < ·)] {a₁ a₂ b₁ b₂ : α} :
    a₁ * b₁ ≤ a₂ * b₂ → a₁ ≤ a₂ ∨ b₁ ≤ b₂ := by
  contrapose!
  -- ⊢ a₂ < a₁ ∧ b₂ < b₁ → a₂ * b₂ < a₁ * b₁
  exact fun h => mul_lt_mul_of_lt_of_lt h.1 h.2
  -- 🎉 no goals
#align le_or_le_of_mul_le_mul le_or_le_of_mul_le_mul
#align le_or_le_of_add_le_add le_or_le_of_add_le_add

@[to_additive]
theorem mul_lt_mul_iff_of_le_of_le [CovariantClass α α (· * ·) (· ≤ ·)]
    [CovariantClass α α (Function.swap (· * ·)) (· ≤ ·)] [CovariantClass α α (· * ·) (· < ·)]
    [CovariantClass α α (Function.swap (· * ·)) (· < ·)] {a₁ a₂ b₁ b₂ : α} (ha : a₁ ≤ a₂)
    (hb : b₁ ≤ b₂) : a₁ * b₁ < a₂ * b₂ ↔ a₁ < a₂ ∨ b₁ < b₂ := by
  refine' ⟨lt_or_lt_of_mul_lt_mul, fun h => _⟩
  -- ⊢ a₁ * b₁ < a₂ * b₂
  cases' h with ha' hb'
  -- ⊢ a₁ * b₁ < a₂ * b₂
  · exact mul_lt_mul_of_lt_of_le ha' hb
    -- 🎉 no goals
  · exact mul_lt_mul_of_le_of_lt ha hb'
    -- 🎉 no goals
#align mul_lt_mul_iff_of_le_of_le mul_lt_mul_iff_of_le_of_le
#align add_lt_add_iff_of_le_of_le add_lt_add_iff_of_le_of_le

end Mul

variable [MulOneClass α]

@[to_additive]
theorem min_le_mul_of_one_le_right [CovariantClass α α (· * ·) (· ≤ ·)] {a b : α} (hb : 1 ≤ b) :
    min a b ≤ a * b :=
  min_le_iff.2 <| Or.inl <| le_mul_of_one_le_right' hb
#align min_le_mul_of_one_le_right min_le_mul_of_one_le_right
#align min_le_add_of_nonneg_right min_le_add_of_nonneg_right

@[to_additive]
theorem min_le_mul_of_one_le_left [CovariantClass α α (Function.swap (· * ·)) (· ≤ ·)] {a b : α}
    (ha : 1 ≤ a) : min a b ≤ a * b :=
  min_le_iff.2 <| Or.inr <| le_mul_of_one_le_left' ha
#align min_le_mul_of_one_le_left min_le_mul_of_one_le_left
#align min_le_add_of_nonneg_left min_le_add_of_nonneg_left

@[to_additive]
theorem max_le_mul_of_one_le [CovariantClass α α (· * ·) (· ≤ ·)]
    [CovariantClass α α (Function.swap (· * ·)) (· ≤ ·)] {a b : α} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    max a b ≤ a * b :=
  max_le_iff.2 ⟨le_mul_of_one_le_right' hb, le_mul_of_one_le_left' ha⟩
#align max_le_mul_of_one_le max_le_mul_of_one_le
#align max_le_add_of_nonneg max_le_add_of_nonneg

end CovariantClassMulLe
