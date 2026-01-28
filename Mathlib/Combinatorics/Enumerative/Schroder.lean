/-
Copyright (c) 2025 Weijie Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weijie Jiang
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Even
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Order.Interval.Finset.Nat

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite
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

* `even_largeSchroder` : The large Schröder numbers are positive and even for `n > 0`.
* `smallSchroder_succ` : A recursive formula for small Schröder numbers:
  `S (n + 1) = 2 * S n + ∑ i < n, S i * S (n - i)`.

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

/-- The small Schröder number is equal to : `largeSchroder n = 2 * smallSchroder n, 1 ≤ n -/
def smallSchroder : ℕ → ℕ
  | 0 => 1
  | n => largeSchroder n / 2

@[simp] lemma smallSchroder_zero : smallSchroder 0 = 1 := by simp [smallSchroder]
@[simp] lemma smallSchroder_one : smallSchroder 1 = 1 := by simp [smallSchroder]

lemma smallSchroder_eq_largeSchroder_div_two (hn : n ≠ 0) :
    smallSchroder n = largeSchroder n / 2 := by
  rw [smallSchroder]
  exact fun x ↦ (fun {a} h ↦ (iff_false_intro h).mp) hn x

lemma two_mul_smallSchroder (hn : n ≠ 0) : 2 * smallSchroder n = largeSchroder n := by
  rw [smallSchroder_eq_largeSchroder_div_two hn,
    Nat.mul_div_cancel_left' (even_largeSchroder (by omega)).two_dvd]

theorem smallSchroder_succ (n : ℕ) :
    smallSchroder (n + 1) =
      smallSchroder n + 2 * ∑ i < n, smallSchroder i * smallSchroder (n - i) := by
  obtain _ | n := n
  · simp only [zero_add, smallSchroder_one, smallSchroder_zero, isMin_iff_eq_bot, bot_eq_zero,
    IsMin.finsetIio_eq, zero_tsub, mul_one, sum_empty, mul_zero, add_zero]
  · refine Nat.mul_left_cancel zero_lt_two ?_
    calc
          2 * smallSchroder (n + 2)
      _ = largeSchroder (n + 1) + ∑ i ≤ n + 1,
        largeSchroder i * largeSchroder (n + 1 - i) := by
          rw [two_mul_smallSchroder (by omega), largeSchroder_succ, Iic_eq_Icc, bot_eq_zero]
      _ = 3 * largeSchroder (n + 1) + ∑ i ∈ Icc 1 n ,
        largeSchroder i * largeSchroder (n + 1 - i) := by
          rw [Iic_eq_Icc, bot_eq_zero, ← Ico_succ_right_eq_Icc, succ_eq_succ, succ_eq_add_one,
            sum_eq_sum_Ico_succ_bot (by omega), ← sum_Ico_add_eq_sum_Ico_add_one (by omega)]
          simp_all only [largeSchroder_zero, tsub_zero, one_mul, zero_add, tsub_self, mul_one]
          rw [add_comm, add_right_comm, ← two_mul, ← add_assoc, add_right_comm]
          congr 1; lia
      _ = 6 * smallSchroder (n + 1) + 4 * ∑ i ∈ Icc 1 n,
        smallSchroder i * smallSchroder (n + 1 - i) := by
          rw [show 6 * smallSchroder (n + 1) = 3 * (2 * smallSchroder (n + 1)) by lia,
            two_mul_smallSchroder (by omega)]
          congr
          rw [mul_sum]
          apply sum_congr rfl; intros k hk; simp only [mem_Icc] at hk
          rw [← two_mul_smallSchroder (by omega), ← two_mul_smallSchroder (by omega)]
          lia
      _ = _ := by
        have h : ∑ i ∈ Icc 1 n, i.smallSchroder * (n + 1 - i).smallSchroder + smallSchroder (n + 1)
          = ∑ i ∈ Iio (n + 1), i.smallSchroder * (n + 1 - i).smallSchroder := by
            rw [Iio_eq_Ico, bot_eq_zero, sum_eq_sum_Ico_succ_bot (by omega)]
            simp only [smallSchroder_zero, tsub_zero, one_mul, zero_add, add_comm]
            congr
        rw [← h]
        lia

theorem smallSchroder_succ_add_smallSchroder (n : ℕ) :
    smallSchroder (n + 1) + smallSchroder n =
      2 * ∑ ij ∈ antidiagonal n, smallSchroder ij.1 * smallSchroder ij.2 := by
  rw [smallSchroder_succ, Iio_eq_range]
  have : 2 * ∑ i ∈ range n, i.smallSchroder * (n - i).smallSchroder + 2 * smallSchroder n =
      2 * ∑ i ∈ range (n + 1), i.smallSchroder * (n - i).smallSchroder := by
    rw [sum_range_succ, tsub_self, smallSchroder_zero, mul_one]
    lia
  rw [add_right_comm, ← two_mul, add_comm, this, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun x y => smallSchroder x * smallSchroder y) n,
    Finset.sum_range, add_comm]

end Nat
