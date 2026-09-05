/-
Copyright (c) 2026 Furkan Efe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Furkan Efe
-/
module

public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Algebra.Order.Field.Basic

/-!
# Tail bounds for sums of binomial coefficients

This file proves an elementary Chernoff-type bound on a tail sum of binomial
coefficients:
`∑ j ∈ Ico m (n + 1), n.choose j ≤ (1 + x) ^ n / x ^ m` for every `x ≥ 1`.

The proof is the classical exponential moment trick, done combinatorially: for
`m ≤ j` and `1 ≤ x` we have `x ^ m ≤ x ^ j`, so the tail sum is bounded by
`x ^ (-m) * ∑ j, n.choose j * x ^ j = x ^ (-m) * (1 + x) ^ n` by the binomial
theorem.

Mathlib already has the *total* sum `Nat.sum_range_choose` and measure-theoretic
Chernoff/Hoeffding bounds in `Mathlib/Probability/Moments/SubGaussian.lean`.
The statement here is purely combinatorial: it needs no probability space and
applies directly to counting arguments.

## Main declarations

* `Nat.sum_Ico_choose_le_div`: `∑ j ∈ Ico m (n + 1), n.choose j ≤ (1 + x) ^ n / x ^ m`
  for `1 ≤ x`.
* `Nat.sum_Ico_choose_le_three_pow_div`: the case `x = 2`, giving the bound
  `3 ^ n / 2 ^ m`.
-/

public section

open Finset

variable {α : Type*}

namespace Nat

/-- The binomial theorem in the form `∑ j ≤ n, n.choose j * x ^ j = (1 + x) ^ n`. -/
theorem sum_range_choose_mul_pow [CommSemiring α] (n : ℕ) (x : α) :
    ∑ j ∈ range (n + 1), (n.choose j : α) * x ^ j = (1 + x) ^ n := by
  rw [add_comm (1 : α) x, add_pow]
  exact Finset.sum_congr rfl fun j _ => by rw [one_pow, mul_one]; ring

variable [Semifield α] [LinearOrder α] [IsStrictOrderedRing α]

/-- **Elementary Chernoff bound for binomial coefficients.**

For every `x ≥ 1`, the tail sum `∑ j ∈ Ico m (n + 1), n.choose j` is bounded by
`(1 + x) ^ n / x ^ m`. Optimizing over `x` gives the usual exponential decay of
binomial tails. -/
theorem sum_Ico_choose_le_div (n m : ℕ) {x : α} (hx : 1 ≤ x) :
    ∑ j ∈ Ico m (n + 1), (n.choose j : α) ≤ (1 + x) ^ n / x ^ m := by
  have hx0 : (0 : α) < x := lt_of_lt_of_le zero_lt_one hx
  have hxm : (0 : α) < x ^ m := pow_pos hx0 m
  have hsub : Ico m (n + 1) ⊆ range (n + 1) := by
    rw [Finset.range_eq_Ico]
    exact Finset.Ico_subset_Ico_left (Nat.zero_le m)
  rw [le_div_iff₀ hxm]
  calc (∑ j ∈ Ico m (n + 1), (n.choose j : α)) * x ^ m
      = ∑ j ∈ Ico m (n + 1), (n.choose j : α) * x ^ m := Finset.sum_mul _ _ _
    _ ≤ ∑ j ∈ Ico m (n + 1), (n.choose j : α) * x ^ j := by
        refine Finset.sum_le_sum fun j hj => ?_
        exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx (Finset.mem_Ico.mp hj).1)
          (by positivity)
    _ ≤ ∑ j ∈ range (n + 1), (n.choose j : α) * x ^ j :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun j _ _ => by positivity
    _ = (1 + x) ^ n := sum_range_choose_mul_pow n x

/-- The case `x = 2` of `Nat.sum_Ico_choose_le_div`:
`∑ j ∈ Ico m (n + 1), n.choose j ≤ 3 ^ n / 2 ^ m`. -/
theorem sum_Ico_choose_le_three_pow_div (n m : ℕ) :
    ∑ j ∈ Ico m (n + 1), (n.choose j : α) ≤ 3 ^ n / 2 ^ m := by
  have h := sum_Ico_choose_le_div (α := α) n m (x := 2) one_le_two
  norm_num at h
  exact h

end Nat
