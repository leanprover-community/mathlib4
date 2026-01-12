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
import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow

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

/-- The small Schröder number is equal to : `largeSchroder n = 2 * smallSchroder n, 1 ≤ n` -/
def smallSchroder : ℕ → ℕ
  | 0 => 1
  | n => largeSchroder n / 2

@[simp] lemma smallSchroder_zero : smallSchroder 0 = 1 := by simp only [smallSchroder]
@[simp] lemma smallSchroder_one : smallSchroder 1 = 1 := by
  simp only [smallSchroder, largeSchroder_one, ofNat_pos, Nat.div_self]

lemma smallSchroder_eq_largeSchroder_div_two (hn : 0 ≠ n) :
    smallSchroder n = largeSchroder n / 2 := by
  rw [smallSchroder]
  intro x
  subst x
  simp_all only [ne_eq, not_true_eq_false]

lemma two_mul_smallSchroder (hn : 0 ≠ n) : 2 * smallSchroder n = largeSchroder n := by
  rw [smallSchroder_eq_largeSchroder_div_two hn,
    Nat.mul_div_cancel_left' (even_largeSchroder (by omega)).two_dvd]

theorem smallSchroder_succ (n : ℕ) :
    smallSchroder (n + 1) =
      smallSchroder n + 2 * ∑ i < n, smallSchroder i * smallSchroder (n - i) := by
  by_cases hn : n = 0
  · subst hn
    simp_all only [zero_add, smallSchroder_one,
      smallSchroder_zero, isMin_iff_eq_bot, Nat.bot_eq_zero,
      IsMin.finsetIio_eq, zero_tsub, mul_one, sum_empty, mul_zero, add_zero]
  · have hnn : 0 < n := by omega
    suffices 2 * smallSchroder (n + 1) =
        2 * smallSchroder n + 4 * ∑ i < n, smallSchroder i * smallSchroder (n - i) by linarith
    have h_sum : 4 * ∑ i < n, smallSchroder i * smallSchroder (n - i) =
        ∑ i ≤ n, largeSchroder i * largeSchroder (n - i) := by
      rw [mul_sum, Iio_eq_Ico, Iic_eq_Icc, Nat.bot_eq_zero, sum_eq_sum_Ico_succ_bot (by omega)]
      have : ∑ k ∈ Ico (0 + 1) n, 4 * (k.smallSchroder * (n - k).smallSchroder) =
          ∑ k ∈ Ico 1 n, largeSchroder k * largeSchroder (n - k) := by
        apply sum_congr rfl; intros k hk; simp only [zero_add, mem_Ico] at hk
        have : 4 * (k.smallSchroder * (n - k).smallSchroder) =
          (2 * k.smallSchroder) * (2 * (n - k).smallSchroder) := by linarith
        rw [this, two_mul_smallSchroder (by omega), two_mul_smallSchroder (by omega)]
      rw [this, smallSchroder_zero, tsub_zero, one_mul, ← add_sum_Ico_eq_sum_Icc (by omega)]
      have Ico_bot : largeSchroder 0 * n.largeSchroder + ∑ k ∈ Ico 1 n,
        k.largeSchroder * (n - k).largeSchroder  =
          ∑ k ∈ Ico 0 n, k.largeSchroder * (n - k).largeSchroder  := by
        rw [sum_eq_sum_Ico_succ_bot hnn]
        simp only [largeSchroder_zero, one_mul, tsub_zero,
          zero_add]
      have : 4 * smallSchroder n = 2 * (2 * smallSchroder n) := by linarith
      rw [this, two_mul_smallSchroder (by omega), two_mul, add_assoc]
      have : n.largeSchroder + ∑ k ∈ Ico 1 n, k.largeSchroder * (n - k).largeSchroder =
          ∑ k ∈ Ico 1 n, k.largeSchroder * (n - k).largeSchroder +
            largeSchroder 0 * n.largeSchroder := by
        simp only [largeSchroder_zero, one_mul, add_comm]
      rw [this]
      simp_all only [zero_add, Ico_zero_eq_range, largeSchroder_zero, one_mul, tsub_self, mul_one]
    rw [two_mul_smallSchroder (by omega), two_mul_smallSchroder (by omega),
      largeSchroder_succ, h_sum, Iic_eq_Icc, Nat.bot_eq_zero]

end Nat
