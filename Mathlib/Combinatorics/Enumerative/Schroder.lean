/-
Copyright (c) 2025 Weijie Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weijie Jiang
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Even
public import Mathlib.Order.Interval.Finset.Nat

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Antidiag.Prod
import Mathlib.Tactic.Linarith

/-!
# Schröder numbers

The Schröder numbers (https://oeis.org/A006318) are a sequence of integers that appear in various
combinatorial contexts.

## Main definitions

* `largeSchroder n`: the `n`th large Schroder number, defined recursively as
  `largeSchroder (n + 1) = largeSchroder n +
    ∑ i : Fin n.succ, largeSchroder i * largeSchroder (n - i)`.
* `smallSchroder n`: the `n`th small Schroder number, defined as
  `smallSchroder n = largeSchroder n / 2` for `n ≠ 1` and `smallSchroder 1 = 1`.

## Main results

* `largeSchroder_pos_even` : The large Schroder numbers are positive and even for `n ≥ 1`.
  `largeSchroder n = 2 * smallSchroder (n + 1)` for `n ≥ 1`.
* `smallSchroder_sum_range` : A recursive formula for small Schroder numbers:
  `smallSchroder (n + 1) =
    3 * smallSchroder n +
      2 * ∑ i ∈ range (n - 2), smallSchroder (i + 2) * smallSchroder (n - 1 - i)`.
-/

@[expose] public section

open Finset

namespace Nat
variable {n : ℕ}

/-- The recursive definition of the sequence of the large Schroder numbers :
`a (n + 1) = a n + ∑ i : Fin n.succ, a i * a (n - i)` -/
def largeSchroder : ℕ → ℕ
  | 0 => 1
  | n + 1 => largeSchroder n + ∑ i : Fin n.succ, largeSchroder i * largeSchroder (n - i)

@[simp] theorem largeSchroder_zero : largeSchroder 0 = 1 := by simp [largeSchroder]
@[simp] theorem largeSchroder_one : largeSchroder 1 = 2 := by simp [largeSchroder]
@[simp] theorem largeSchroder_two : largeSchroder 2 = 6 := by simp [largeSchroder]

theorem largeSchroder_succ (n : ℕ) :
    largeSchroder (n + 1) = largeSchroder n + ∑ i ≤ n, largeSchroder i * largeSchroder (n - i) := by
  rw [largeSchroder, Iic_eq_Icc]
  simp only [succ_eq_add_one, Nat.bot_eq_zero, Nat.add_left_cancel_iff]
  rw [Icc_eq_range', ← Ico_eq_range']
  simp [sum_range]

theorem largeSchroder_succ_range (n : ℕ) :
    largeSchroder (n + 1) =
      largeSchroder n + ∑ i ∈ range (n + 1), largeSchroder i * largeSchroder (n - i) := by
  rw [largeSchroder_succ, Iic_eq_Icc]
  simp only [Nat.bot_eq_zero, Nat.add_left_cancel_iff]
  rw [Icc_eq_range', ← Ico_eq_range']
  simp [sum_range]

theorem even_largeSchroder : ∀ {n : ℕ}, n ≠ 0 → Even (largeSchroder n)
  | 1, _ => by simp
  | n + 2, _ => by
    rw [largeSchroder_succ]
    refine .add (even_largeSchroder n.succ_ne_zero) <| even_sum _ fun k hk ↦ ?_
    obtain _ | k := k
    · simpa using even_largeSchroder n.succ_ne_zero
    have : k < n + 1 := by simp at hk; lia
    exact .mul_right (even_largeSchroder k.succ_ne_zero) _

/-- The small Schroder number is equal to : `largeSchroder n = 2 * smallSchroder (n + 1), n ≥ 1` -/
def smallSchroder : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n + 1 => largeSchroder n / 2

@[simp] lemma smallSchroder_zero : smallSchroder 0 = 1 := by simp [smallSchroder]
@[simp] lemma smallSchroder_one : smallSchroder 1 = 1 := by simp [smallSchroder]

lemma smallSchroder_succ (h : n ≠ 0) : smallSchroder (n + 1) = largeSchroder n / 2 := by
  simp [smallSchroder]

lemma two_mul_smallSchroder_succ (hn : n ≠ 0) : 2 * smallSchroder (n + 1) = largeSchroder n := by
  rw [smallSchroder_succ hn, Nat.mul_div_cancel_left' (even_largeSchroder hn).two_dvd]

theorem smallSchroder_eq_sum_range (hn : 1 < n) :
  smallSchroder (n + 1) =
    3 * smallSchroder n +
      2 * ∑ i ∈ range (n - 2), smallSchroder (i + 2) * smallSchroder (n - 1 - i) := by
  have h := largeSchroder_succ_range (n - 1)
  nth_rw 1 [show n - 1 + 1 = n by lia] at h
  have sum_eq : ∑ i ∈ range (n - 1 + 1), largeSchroder i * largeSchroder (n - 1 - i) =
    2 * largeSchroder (n - 1) + ∑ i ∈ Ico 1 (n - 1),
      largeSchroder i * largeSchroder (n - 1 - i) := by
    rw [sum_range_succ, show n - 1 = n - 2 + 1 by lia, sum_range_succ', sum_Ico_eq_sum_range,
      show n - 2 + 1 = n - 1 by lia, show n - 1 - 1 = n - 2 by lia]
    simp only [largeSchroder_zero, tsub_zero, one_mul, tsub_self, mul_one]
    rw [add_assoc, ← two_mul, add_comm]
    congr 1; apply sum_congr rfl; intro x hx; simp at hx
    rw [add_comm x 1]
  rw [sum_eq] at h
  have sum_eq' : ∑ i ∈ Ico 1 (n - 1), largeSchroder i * largeSchroder (n - 1 - i) =
    4 * ∑ i ∈ Ico 1 (n - 1), smallSchroder (i + 1) * smallSchroder (n - i) := by
    rw [mul_sum]
    apply sum_congr rfl; intro x hx; simp at hx
    rw [← two_mul_smallSchroder_succ (by lia), ← two_mul_smallSchroder_succ (by lia),
      show n - 1 - x + 1 = n - x by lia]
    linarith
  rw [sum_eq', ← two_mul_smallSchroder_succ (by lia), ← two_mul_smallSchroder_succ (by lia)]
    at h
  have h' : 2 * smallSchroder (n - 1 + 1) +
    (2 * (2 * smallSchroder (n - 1 + 1)) +
      4 * ∑ i ∈ Ico 1 (n - 1), smallSchroder (i + 1) * smallSchroder (n - i)) =
    2 * (smallSchroder n + 2 * (smallSchroder n +
      ∑ i ∈ Ico 1 (n - 1), smallSchroder (i + 1) * smallSchroder (n - i))) := by lia
  simp only [h', mul_eq_mul_left_iff, OfNat.ofNat_ne_zero, or_false] at h
  rw [h, sum_Ico_eq_sum_range]
  lia

end Nat
