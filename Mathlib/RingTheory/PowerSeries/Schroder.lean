/-
Copyright (c) 2025 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weijie Jiang
-/

import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.PowerSeries.WellKnown

open Finset BigOperators

namespace PowerSeries

/-- The power series for large Schröder numbers -/
def largeSchroderPowerSeries : PowerSeries ℕ :=
  PowerSeries.mk largeSchroder

@[simp]
lemma largeSchroderPowerSeries_coeff (n : ℕ) :
  (coeff n) largeSchroderPowerSeries = largeSchroder n := by
  simp [largeSchroderPowerSeries]

@[simp]
lemma largeSchroderPowerSeries_constantCoeff :
  constantCoeff largeSchroderPowerSeries = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [largeSchroderPowerSeries_coeff, largeSchroder_zero]

@[simp]
lemma largeSchroder_sum_coeff (n : ℕ) (hn : 0 < n) :
  ∑ i ∈ range (n + 1), coeff i X * largeSchroder (n - i) =
    largeSchroder (n - 1) := by
  simp [coeff_X]
  aesop

@[simp]
lemma X_mul_largeSchroder_coeff (n : ℕ) (hn : 0 < n) :
  coeff n (X * largeSchroderPowerSeries) = largeSchroder (n - 1) := by
  simp [coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ
    (fun x y => coeff x X * largeSchroder y)]
  rw [largeSchroder_sum_coeff n hn]

lemma X_mul_largeSchroder_pow_coeff (n : ℕ) (hn : 0 < n) :
  coeff n (X * largeSchroderPowerSeries ^ 2) =
    ∑ i ∈ range n, largeSchroder i * largeSchroder (n - 1 - i) := by
  rw [pow_two, ← mul_assoc, coeff_mul]
  rw [Nat.sum_antidiagonal_eq_sum_range_succ
    (fun x y => (coeff x) (X * largeSchroderPowerSeries) * (coeff y) largeSchroderPowerSeries) n,
    Nat.succ_eq_add_one, sum_range_succ]
  simp [X_mul_largeSchroder_coeff n hn]
  have : ∑ x ∈ range n, (coeff x) (X * largeSchroderPowerSeries) * largeSchroder (n - x)  =
    ∑ x ∈ range n, if 0 < x then largeSchroder (x - 1) * largeSchroder (n - x) else 0 := by
    apply sum_congr rfl
    intro x a
    simp_all only [mem_range]
    split
    next h =>
      simp_all only [mul_eq_mul_right_iff]
      simp [X_mul_largeSchroder_coeff x (by omega)]
    next h =>
      simp_all only [not_lt, nonpos_iff_eq_zero, coeff_zero_eq_constantCoeff, map_mul,
      constantCoeff_X, largeSchroderPowerSeries_constantCoeff, mul_one, tsub_zero, zero_mul]
  rw [this, sum_range_eq_add_Ico _ (by omega)]
  simp only [lt_self_iff_false, reduceIte, zero_add]
  have : (∑ x ∈ Ico 1 n, if 0 < x then largeSchroder (x - 1) * largeSchroder (n - x) else 0) =
    ∑ x ∈ Ico 1 n, largeSchroder (x - 1) * largeSchroder (n - x) := by
    apply sum_congr rfl
    intros x hx
    simp at hx
    have hx' : 0 < x := by omega
    rw [if_pos hx']
  rw [this, sum_Ico_eq_sum_range, show n = n - 1 + 1 by omega,
    sum_range_succ, show n - 1 + 1 = n by omega]
  simp only [add_tsub_cancel_left, tsub_self, largeSchroder_zero, mul_one, Nat.add_right_cancel_iff]
  apply sum_congr rfl
  intros x hx
  simp at hx
  have : n - 1 - x = n - (1 + x) := by omega
  rw [this]

theorem largeSchroder_eq_one_add_X_mul_largeSchroder_add_X_mul_largeSchroder_pow :
  largeSchroderPowerSeries = 1 + X * largeSchroderPowerSeries +
    X * largeSchroderPowerSeries ^ 2 := by
  ext n
  by_cases hn : n = 0
  · aesop
  · have hn' : 0 < n := by omega
    simp [largeSchroderPowerSeries_coeff, hn]
    rw [X_mul_largeSchroder_pow_coeff _ hn', X_mul_largeSchroder_coeff _ hn',
      show n = n - 1 + 1 by omega, largeSchroder_succ_range (n - 1), show n - 1 + 1 = n by omega]


def smallSchroderPowerSeries : PowerSeries ℚ :=
  PowerSeries.mk smallSchroder

@[simp]
lemma smallSchroderPowerSeries_coeff (n : ℕ) :
  (coeff n) smallSchroderPowerSeries = smallSchroder n := by
  simp [smallSchroderPowerSeries]

@[simp]
lemma smallSchroderPowerSeries_constantCoeff :
  constantCoeff smallSchroderPowerSeries = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [smallSchroderPowerSeries_coeff, smallSchroder_zero]

@[simp]
lemma smallSchroder_sum_coeff (n : ℕ) (hn : 0 < n) :
  ∑ i ∈ range (n + 1), coeff i X * smallSchroder (n - i) =
    smallSchroder (n - 1) := by
  simp [coeff_X]
  aesop

@[simp]
lemma X_mul_smallSchroder_coeff (n : ℕ) (hn : 0 < n) :
  coeff n (X * smallSchroderPowerSeries) = smallSchroder (n - 1) := by
  simp [coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ
    (fun x y => coeff x X * smallSchroder y)]
  rw [smallSchroder_sum_coeff n hn]

lemma two_mul_smallSchroder_eq_largeSchroder_coeff (n : ℕ) (hn : 1 ≤ n) :
  2 * coeff (n + 1) (smallSchroderPowerSeries) = coeff n (largeSchroderPowerSeries) := by
  simp [smallSchroderPowerSeries_coeff,
    largeSchroder_eq_smallSchroder_succ_mul_two (by omega), mul_comm]

lemma X_mul_smallSchroder_pow_coeff (n : ℕ) (hn : 1 ≤ n) :
  coeff n (X * smallSchroderPowerSeries ^ 2) =
    ∑ i ∈ range n, smallSchroder i * smallSchroder (n - 1 - i) := by
  rw [pow_two, ← mul_assoc, coeff_mul]
  rw [Nat.sum_antidiagonal_eq_sum_range_succ
    (fun x y => (coeff x) (X * smallSchroderPowerSeries) * (coeff y) smallSchroderPowerSeries) n,
    Nat.succ_eq_add_one, sum_range_succ]
  simp [X_mul_smallSchroder_coeff n hn]
  have : ∑ x ∈ range n, (coeff x) (X * smallSchroderPowerSeries) * smallSchroder (n - x)  =
    ∑ x ∈ range n, if 0 < x then smallSchroder (x - 1) * smallSchroder (n - x) else 0 := by
    apply sum_congr rfl
    intro x a
    simp_all only [mem_range]
    split
    next h =>
      simp_all only [mul_eq_mul_right_iff]
      simp [X_mul_smallSchroder_coeff x (by omega)]
    next h =>
      simp_all only [not_lt, nonpos_iff_eq_zero, coeff_zero_eq_constantCoeff, map_mul,
      constantCoeff_X, smallSchroderPowerSeries_constantCoeff, tsub_zero, zero_mul]
  rw [this, sum_range_eq_add_Ico _ (by omega)]
  simp only [lt_self_iff_false, reduceIte, zero_add]
  have : (∑ x ∈ Ico 1 n, if 0 < x then smallSchroder (x - 1) * smallSchroder (n - x) else 0) =
    ∑ x ∈ Ico 1 n, smallSchroder (x - 1) * smallSchroder (n - x) := by
    apply sum_congr rfl
    intros x hx
    simp at hx
    have hx' : 0 < x := by omega
    rw [if_pos hx']
  rw [this, sum_Ico_eq_sum_range, show n = n - 1 + 1 by omega,
    sum_range_succ, show n - 1 + 1 = n by omega,
      show n - 1 - (n - 1) = 0 by omega, smallSchroder_zero]
  congr 1
  · apply sum_congr rfl
    intros x hx
    simp at hx
    rw [show 1 + x - 1 = x by omega, show n - (1 + x) = n - 1 - x by omega]
  · rw [mul_one]

end PowerSeries
