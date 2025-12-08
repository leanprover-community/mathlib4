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
# Schroder numbers

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


open Finset Nat

open Finset.antidiagonal (fst_le snd_le)

/-- The recursive definition of the sequence of the large Schroder numbers :
`a (n + 1) = a n + ∑ i : Fin n.succ, a i * a (n - i)` -/
def largeSchroder : ℕ → ℕ
  | 0 => 1
  | n + 1 =>
    largeSchroder n +
      ∑ i : Fin n.succ, largeSchroder i * largeSchroder (n - i)

@[simp]
theorem largeSchroder_zero : largeSchroder 0 = 1 := by
  simp [largeSchroder]

@[simp]
theorem largeSchroder_one : largeSchroder 1 = 2 := by
  simp [largeSchroder]

@[simp]
theorem largeSchroder_two : largeSchroder 2 = 6 := by
  simp [largeSchroder]

theorem largeSchroder_succ (n : ℕ) :
  largeSchroder (n + 1) = largeSchroder n +
    ∑ i ≤ n, largeSchroder i * largeSchroder (n - i) := by
  rw [largeSchroder, Iic_eq_Icc]
  simp only [succ_eq_add_one, Nat.bot_eq_zero, Nat.add_left_cancel_iff]
  rw [Icc_eq_range', ← Ico_eq_range']
  simp [sum_range]

theorem largeSchroder_succ_range (n : ℕ) :
  largeSchroder (n + 1) = largeSchroder n +
    ∑ i ∈ range (n + 1), largeSchroder i * largeSchroder (n - i) := by
  rw [largeSchroder_succ]
  rw [Iic_eq_Icc]
  simp only [Nat.bot_eq_zero, Nat.add_left_cancel_iff]
  rw [Icc_eq_range', ← Ico_eq_range']
  simp [sum_range]

theorem largeSchroder_pos_even (n : ℕ) (hn : 1 ≤ n) : Even (largeSchroder n) := by
  induction n using Nat.case_strong_induction_on with
  | hz => simp at hn
  | hi n ih =>
    by_cases hn' : n = 0
    · aesop
    · have hn : 1 ≤ n := by omega
      rw [largeSchroder_succ n]
      have h_sum_even : Even (∑ i ≤ n, largeSchroder i * largeSchroder (n - i)) := by
        rw [Iic_eq_Icc]
        simp only [Nat.bot_eq_zero]
        rw [Icc_eq_range', ← Ico_eq_range']
        have h1 : ∀ i ∈ Ico 1 n, Even (largeSchroder i * largeSchroder (n - i)) := by
          intro i hi
          refine even_mul.mpr ?_
          left
          simp at hi
          rcases hi with ⟨hi1, hi2⟩
          exact ih (by omega) (by omega) hi1
        rw [sum_Ico_succ_top (by omega)]
        apply Even.add _ (by aesop)
        rw [sum_eq_sum_Ico_succ_bot (by omega)]
        simp only [largeSchroder_zero, tsub_zero, one_mul, zero_add]
        apply Even.add (by aesop)
        exact even_sum (fun i ↦ largeSchroder i * largeSchroder (n - i)) h1
      have h_largeSchroder_n_even : Even (largeSchroder n) := by
        simp_all only [le_add_iff_nonneg_left, _root_.zero_le, le_refl]
      exact Even.add h_largeSchroder_n_even h_sum_even

/-- The small Schroder number is equal to : `largeSchroder n = 2 * smallSchroder (n + 1), n ≥ 1` -/
def smallSchroder (n : ℕ) : ℕ :=
  match n with
  | 0 => 1
  | 1 => 1
  | n + 1 => largeSchroder n / 2

@[simp]
theorem smallSchroder_zero : smallSchroder 0 = 1 := by
  simp only [smallSchroder]

@[simp]
theorem smallSchroder_one : smallSchroder 1 = 1 := by
  simp only [smallSchroder]

theorem largeSchroder_eq_smallSchroder_succ_mul_two {n : ℕ} (h : 1 ≤ n) :
  largeSchroder n = smallSchroder (n + 1) * 2 := by
  simp only [smallSchroder]
  split
  next n_1 heq => simp_all only [Nat.add_eq_zero_iff, one_ne_zero, and_false]
  next n_1 heq =>
    simp_all only [Nat.add_eq_right, largeSchroder_zero, one_mul, OfNat.one_ne_ofNat,
      nonpos_iff_eq_zero, one_ne_zero]
  next n_1 n_2 x heq =>
    simp_all only [imp_false, succ_eq_add_one, Nat.add_right_cancel_iff]
    subst heq
    exact Eq.symm (div_two_mul_two_of_even (largeSchroder_pos_even n (by omega)))

theorem smallSchroder_succ_eq_largeSchroder_div_two {n : ℕ} (h : 1 ≤ n) :
  smallSchroder (n + 1) = largeSchroder n / 2 := by
  simp only [smallSchroder]
  aesop

theorem smallSchroder_sum_range (n : ℕ) (hn : 1 < n) :
  smallSchroder (n + 1) =
    3 * smallSchroder n +
      2 * ∑ i ∈ range (n - 2), smallSchroder (i + 2) * smallSchroder (n - 1 - i) := by
  by_cases hn' : n = 1
  · simp [hn']
    aesop
  · have hn : 2 ≤ n := by omega
    obtain h_largeSchroder_succ := largeSchroder_succ_range (n - 1)
    nth_rw 1 [show n - 1 + 1 = n by omega] at h_largeSchroder_succ
    have sum_eq : ∑ i ∈ range (n - 1 + 1), largeSchroder i * largeSchroder (n - 1 - i) =
      2 * largeSchroder (n - 1) + ∑ i ∈ Ico 1 (n - 1),
        largeSchroder i * largeSchroder (n - 1 - i) := by
      rw [sum_range_succ, show n - 1 = n - 2 + 1 by omega, sum_range_succ', sum_Ico_eq_sum_range,
        show n - 2 + 1 = n - 1 by omega, show n - 1 - 1 = n - 2 by omega]
      simp only [largeSchroder_zero, tsub_zero, one_mul, tsub_self, mul_one]
      rw [add_assoc, ← two_mul, add_comm]
      congr 1; apply sum_congr rfl; intro x hx; simp at hx
      rw [add_comm x 1]
    rw [sum_eq] at h_largeSchroder_succ
    have sum_eq' : ∑ i ∈ Ico 1 (n - 1), largeSchroder i * largeSchroder (n - 1 - i) =
      4 * ∑ i ∈ Ico 1 (n - 1), smallSchroder (i + 1) * smallSchroder (n - i) := by
      rw [mul_sum]
      apply sum_congr rfl; intro x hx; simp at hx
      rw [largeSchroder_eq_smallSchroder_succ_mul_two (by omega),
        largeSchroder_eq_smallSchroder_succ_mul_two (by omega), show n - 1 - x + 1 = n - x by omega]
      linarith
    rw [sum_eq', largeSchroder_eq_smallSchroder_succ_mul_two (by omega),
      largeSchroder_eq_smallSchroder_succ_mul_two (by omega)] at h_largeSchroder_succ
    have h_largeSchroder_succ' : smallSchroder (n - 1 + 1) * 2 +
      (2 * (smallSchroder (n - 1 + 1) * 2) +
        4 * ∑ i ∈ Ico 1 (n - 1), smallSchroder (i + 1) * smallSchroder (n - i)) =
      (smallSchroder n + 2 * (smallSchroder n +
        ∑ i ∈ Ico 1 (n - 1), smallSchroder (i + 1) * smallSchroder (n - i))) * 2 := by
      rw [show n - 1 + 1 = n by omega]
      omega
    rw [h_largeSchroder_succ'] at h_largeSchroder_succ
    simp only [mul_eq_mul_right_iff, OfNat.ofNat_ne_zero, or_false] at h_largeSchroder_succ
    rw [h_largeSchroder_succ, sum_Ico_eq_sum_range, show n - 1 - 1 = n - 2 by omega]
    have : ∑ k ∈ range (n - 2), smallSchroder (1 + k + 1) * smallSchroder (n - (1 + k)) =
      ∑ k ∈ range (n - 2), smallSchroder (k + 2) * smallSchroder (n - 1 - k) := by
      apply sum_congr rfl; intro x hx; simp at hx
      rw [show 1 + x + 1 = x + 2 by omega, show n - (1 + x) = n - 1 - x by omega]
    rw [this]
    omega
