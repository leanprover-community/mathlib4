/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl

! This file was ported from Lean 3 source module algebra.order.monoid.min_max
! leanprover-community/mathlib commit 70d50ecfd4900dd6d328da39ab7ebd516abe4025
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Order.MinMax
import Mathlib.Algebra.Order.Monoid.Lemmas
import Mathlib.Tactic.Contrapose

/-!
# Lemmas about `min` and `max` in an ordered monoid.
-/


variable {α β : Type _}

/-! Some lemmas about types that have an ordering and a binary operation, with no
  rules relating them. -/


@[to_additive]
theorem fn_min_mul_fn_max [LinearOrder α] [CommSemigroup β] (f : α → β) (n m : α) :
    f (min n m) * f (max n m) = f n * f m := by cases' le_total n m with h h <;> simp [h, mul_comm]
#align fn_min_mul_fn_max fn_min_mul_fn_max

@[to_additive]
theorem min_mul_max [LinearOrder α] [CommSemigroup α] (n m : α) : min n m * max n m = n * m :=
  fn_min_mul_fn_max id n m
#align min_mul_max min_mul_max

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

@[to_additive]
theorem max_mul_mul_left (a b c : α) : max (a * b) (a * c) = a * max b c :=
  (monotone_id.const_mul' a).map_max.symm
#align max_mul_mul_left max_mul_mul_left

@[to_additive]
theorem lt_or_lt_of_mul_lt_mul [CovariantClass α α (Function.swap (· * ·)) (· ≤ ·)] {a b m n : α}
    (h : m * n < a * b) : m < a ∨ n < b := by
  contrapose! h
  exact mul_le_mul' h.1 h.2
#align lt_or_lt_of_mul_lt_mul lt_or_lt_of_mul_lt_mul

@[to_additive]
theorem mul_lt_mul_iff_of_le_of_le [CovariantClass α α (Function.swap (· * ·)) (· < ·)]
    [CovariantClass α α (· * ·) (· < ·)] [CovariantClass α α (Function.swap (· * ·)) (· ≤ ·)]
    {a b c d : α} (ac : a ≤ c) (bd : b ≤ d) : a * b < c * d ↔ a < c ∨ b < d := by
  refine' ⟨lt_or_lt_of_mul_lt_mul, fun h => _⟩
  cases' h with ha hb
  · exact mul_lt_mul_of_lt_of_le ha bd
  · exact mul_lt_mul_of_le_of_lt ac hb
#align mul_lt_mul_iff_of_le_of_le mul_lt_mul_iff_of_le_of_le

end Left

section Right

variable [CovariantClass α α (Function.swap (· * ·)) (· ≤ ·)]

@[to_additive]
theorem min_mul_mul_right (a b c : α) : min (a * c) (b * c) = min a b * c :=
  (monotone_id.mul_const' c).map_min.symm
#align min_mul_mul_right min_mul_mul_right

@[to_additive]
theorem max_mul_mul_right (a b c : α) : max (a * c) (b * c) = max a b * c :=
  (monotone_id.mul_const' c).map_max.symm
#align max_mul_mul_right max_mul_mul_right

end Right

end Mul

variable [MulOneClass α]

@[to_additive]
theorem min_le_mul_of_one_le_right [CovariantClass α α (· * ·) (· ≤ ·)] {a b : α} (hb : 1 ≤ b) :
    min a b ≤ a * b :=
  min_le_iff.2 <| Or.inl <| le_mul_of_one_le_right' hb
#align min_le_mul_of_one_le_right min_le_mul_of_one_le_right

@[to_additive]
theorem min_le_mul_of_one_le_left [CovariantClass α α (Function.swap (· * ·)) (· ≤ ·)] {a b : α}
    (ha : 1 ≤ a) : min a b ≤ a * b :=
  min_le_iff.2 <| Or.inr <| le_mul_of_one_le_left' ha
#align min_le_mul_of_one_le_left min_le_mul_of_one_le_left

@[to_additive]
theorem max_le_mul_of_one_le [CovariantClass α α (· * ·) (· ≤ ·)]
    [CovariantClass α α (Function.swap (· * ·)) (· ≤ ·)] {a b : α} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    max a b ≤ a * b :=
  max_le_iff.2 ⟨le_mul_of_one_le_right' hb, le_mul_of_one_le_left' ha⟩
#align max_le_mul_of_one_le max_le_mul_of_one_le

end CovariantClassMulLe
