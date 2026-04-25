/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Ring.Periodic

/-!
# Sums of antiperiodic functions over intervals

This file collects lemmas about `Finset` sums of `Function.Antiperiodic` functions.

## Main results

* `Function.Antiperiodic.sum_Ico_shift`: For an antiperiodic function `f` with antiperiod `c`,
  the sum of `f` over the shifted interval `[a + c, b + c)` equals the negation of the sum
  over `[a, b)`.
* `Function.Antiperiodic.sum_Ico_mul_add_sum_Ico_mul_shift_eq_zero`: A bilinear cancellation
  variant: if `w` is antiperiodic with antiperiod `c`, then summing `w k * f k` over
  `[a + c, b + c)` cancels with summing `w k * f (k + c)` over `[a, b)`.
-/

public section

open Finset

namespace Function.Antiperiodic

variable {α R : Type*}
  [AddCommMonoid α] [PartialOrder α] [IsOrderedCancelAddMonoid α]
  [ExistsAddOfLE α] [LocallyFiniteOrder α]
  [NonAssocRing R]

/-- Shifting the index of summation of an antiperiodic function by its antiperiod negates the
sum. -/
theorem sum_Ico_shift {f : α → R} {c : α} (hf : Antiperiodic f c) (a b : α) :
    ∑ k ∈ Ico (a + c) (b + c), f k = -∑ k ∈ Ico a b, f k := by
  rw [← Finset.sum_Ico_add' f a b c]
  simp_rw [hf _, Finset.sum_neg_distrib]

/-- For `w` antiperiodic with antiperiod `c`, the weighted sum `w k * f k` over `[a + c, b + c)`
and the shifted-argument weighted sum `w k * f (k + c)` over `[a, b)` add to zero. -/
theorem sum_Ico_mul_add_sum_Ico_mul_shift_eq_zero
    {w : α → R} {c : α} (hw : Antiperiodic w c) (f : α → R) (a b : α) :
    ∑ k ∈ Ico (a + c) (b + c), w k * f k +
      ∑ k ∈ Ico a b, w k * f (k + c) = 0 := by
  rw [← Finset.sum_Ico_add' (fun x => w x * f x) a b c]
  simp_rw [hw _, neg_mul, Finset.sum_neg_distrib, neg_add_cancel]

end Function.Antiperiodic
