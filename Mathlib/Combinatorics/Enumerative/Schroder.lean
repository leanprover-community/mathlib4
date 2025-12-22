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

* `largeSchroder n`: the `n`th large Schröder number, defined recursively as `L 0 = 1` and
  `L (n + 1) = L n + ∑ i ≤ n, L i * L (n - i)`.
* `smallSchroder n`: the `n`th small Schröder number, defined as `S 0 = 1` and `S n = L n / 2`
  for `n > 0`.

## Main results

* `largeSchroder_even` : The large Schröder numbers are positive and even for `n > 0`.
* `smallSchroder_succ` : A recursive formula for small Schröder numbers:
  `S (n + 1) = 3 * S n + 2 * ∑ i < n - 2, S (i + 2) * S (n - 1 - i)`.

## Tags

Schroeder, Schroder
-/

@[expose] public section

open Finset

namespace Nat
variable {n : ℕ}

/-- The recursive definition of the sequence of the large Schröder numbers :
`a (n + 1) = a n + ∑ i : Fin n.succ, a i * a (n - i)` -/
def largeSchroder : ℕ → ℕ
  | 0 => 1
  | n + 1 => largeSchroder n + ∑ i : Fin n.succ, largeSchroder i * largeSchroder (n - i)

@[simp] theorem largeSchroder_zero : largeSchroder 0 = 1 := by simp [largeSchroder]
@[simp] theorem largeSchroder_one : largeSchroder 1 = 2 := by simp [largeSchroder]
@[simp] theorem largeSchroder_two : largeSchroder 2 = 6 := by simp [largeSchroder]

theorem largeSchroder_succ (n : ℕ) :
    largeSchroder (n + 1) = largeSchroder n + ∑ i ≤ n, largeSchroder i * largeSchroder (n - i) := by
  simp [largeSchroder, ← Iio_add_one_eq_Iic, Nat.Iio_eq_range, ← Fin.sum_univ_eq_sum_range]

theorem even_largeSchroder : ∀ {n : ℕ}, n ≠ 0 → Even (largeSchroder n)
  | 1, _ => by simp
  | n + 2, _ => by
    rw [largeSchroder_succ]
    refine .add (even_largeSchroder n.succ_ne_zero) <| even_sum _ fun k hk ↦ ?_
    obtain _ | k := k
    · simpa using even_largeSchroder n.succ_ne_zero
    have : k < n + 1 := by simp at hk; lia
    exact .mul_right (even_largeSchroder k.succ_ne_zero) _

/-- The small Schröder number is equal to : `largeSchroder n = 2 * smallSchroder (n + 1), n ≥ 1` -/
def smallSchroder : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n + 1 => largeSchroder n / 2

@[simp] lemma smallSchroder_zero : smallSchroder 0 = 1 := by simp [smallSchroder]
@[simp] lemma smallSchroder_one : smallSchroder 1 = 1 := by simp [smallSchroder]

lemma smallSchroder_succ_eq_largeSchroder_div_two (h : n ≠ 0) :
    smallSchroder (n + 1) = largeSchroder n / 2 := by simp [smallSchroder]

lemma two_mul_smallSchroder_succ (hn : n ≠ 0) : 2 * smallSchroder (n + 1) = largeSchroder n := by
  rw [smallSchroder_succ_eq_largeSchroder_div_two hn,
    Nat.mul_div_cancel_left' (even_largeSchroder hn).two_dvd]

theorem smallSchroder_succ (hn : 1 < n) :
    smallSchroder (n + 1) =
      3 * n.smallSchroder +
          2 * ∑ i ∈ Ioo 0 (n - 1), (i + 1).smallSchroder * (n - i).smallSchroder := by
  obtain _ | _ | n := n
  · simp at hn
  · simp at hn
  refine Nat.mul_left_cancel zero_lt_two ?_
  calc
        2 * (n + 3).smallSchroder
    _ = 3 * (n + 1).largeSchroder +
          ∑ i ∈ Ioo 0 (n + 1), i.largeSchroder * (n + 1 - i).largeSchroder := by
      rw [two_mul_smallSchroder_succ, largeSchroder_succ, ← Icc_bot, ← sum_Ioc_add_eq_sum_Icc,
        ← sum_Ioo_add_eq_sum_Ioc] <;> simp; lia
    _ = 3 * (n + 1).largeSchroder +
          ∑ i ∈ Ioo 0 (n + 1), (2 * (i + 1).smallSchroder) * (2 * (n + 2 - i).smallSchroder) := by
      congr! 2 with i hi
      simp at hi
      rw [← two_mul_smallSchroder_succ, ← two_mul_smallSchroder_succ] <;> lia
    _ = 6 * (n + 2).smallSchroder +
          4 * ∑ i ∈ Ioo 0 (n + 1), (i + 1).smallSchroder * (n + 2 - i).smallSchroder := by
      rw [← two_mul_smallSchroder_succ (by lia)]
      simp [mul_mul_mul_comm _ _ 2, ← Finset.mul_sum]
      lia
    _ = _ := by lia

end Nat
