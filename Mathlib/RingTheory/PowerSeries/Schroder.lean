/-
Copyright (c) 2025 Weijie Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weijie Jiang
-/
module

public import Mathlib.Combinatorics.Enumerative.Schroder
public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Schröder Numbers Power Series

This file defines lemmas and theorems about the power series for large and small Schröder numbers.

## Main Definitions
* `PowerSeries.largeSchroderSeries`: The power series for large Schröder numbers.
* `PowerSeries.smallSchroderSeries`: The power series for small Schröder numbers.

## Main Results
* `largeSchroderSeries_eq_one_add_X_mul_largeSchroderSeries_add_X_mul_largeSchroderSeries_sq`:
  The functional equation for the large Schröder numbers power series.

## TODO

* Prove the small Schröder numbers power series.

-/

@[expose] public section

open Finset Nat

namespace PowerSeries

/-- The power series for large Schröder numbers -/
def largeSchroderSeries : PowerSeries ℕ :=
  PowerSeries.mk largeSchroder

@[simp]
lemma coeff_largeSchroderSeries (n : ℕ) :
    (coeff n) largeSchroderSeries = largeSchroder n := by
  simp [largeSchroderSeries]

@[simp]
lemma constantCoeff_largeSchroderSeries :
    constantCoeff largeSchroderSeries = 1 := by
  simp only [← coeff_zero_eq_constantCoeff_apply, coeff_largeSchroderSeries, largeSchroder_zero]

@[simp]
lemma coeff_X_mul_largeSchroderSeries (n : ℕ) (hn : 0 < n) :
    coeff n (X * largeSchroderSeries) = largeSchroder (n - 1) := by
  simp only [coeff_mul, coeff_largeSchroderSeries,
    Nat.sum_antidiagonal_eq_sum_range_succ (coeff · X * largeSchroder ·),
    succ_eq_add_one]
  simp only [coeff_X, ite_mul, one_mul, zero_mul, sum_ite_eq', mem_range, lt_add_iff_pos_left,
    ite_eq_left_iff, not_lt, nonpos_iff_eq_zero]
  rintro rfl
  simp_all only [lt_self_iff_false]

lemma coeff_X_mul_largeSchroderSeriesSeries_sq (n : ℕ) (hn : 0 < n) :
    coeff n (X * largeSchroderSeries ^ 2) =
      ∑ i ∈ range n, largeSchroder i * largeSchroder (n - 1 - i) := by
  rw [pow_two, ← mul_assoc, coeff_mul]
  rw [Nat.sum_antidiagonal_eq_sum_range_succ
    (fun x y => (coeff x) (X * largeSchroderSeries) * (coeff y) largeSchroderSeries) n,
    Nat.succ_eq_add_one, sum_range_succ]
  simp only [coeff_largeSchroderSeries, coeff_X_mul_largeSchroderSeries n hn, tsub_self,
    largeSchroder_zero, mul_one]
  have : ∑ x ∈ range n, (coeff x) (X * largeSchroderSeries) * largeSchroder (n - x) =
      ∑ x ∈ range n, if 0 < x then largeSchroder (x - 1) * largeSchroder (n - x) else 0 := by
    apply sum_congr rfl
    intro x a
    simp_all only [mem_range]
    split
    next h =>
      simp_all only [mul_eq_mul_right_iff]
      simp [coeff_X_mul_largeSchroderSeries x (by omega)]
    next h =>
      simp_all only [not_lt, nonpos_iff_eq_zero, coeff_zero_eq_constantCoeff, map_mul,
      constantCoeff_X, constantCoeff_largeSchroderSeries, mul_one, tsub_zero, zero_mul]
  rw [this, sum_range_eq_add_Ico _ (by omega)]
  simp only [lt_self_iff_false, reduceIte, zero_add]
  have : (∑ x ∈ Ico 1 n, if 0 < x then largeSchroder (x - 1) * largeSchroder (n - x) else 0) =
    ∑ x ∈ Ico 1 n, largeSchroder (x - 1) * largeSchroder (n - x) := by
    apply sum_congr rfl
    intros x hx
    have hx' : 0 < x := by grind
    rw [if_pos hx']
  rw [this, sum_Ico_eq_sum_range, show n = n - 1 + 1 by omega,
    sum_range_succ]
  grind [largeSchroder_zero]

theorem largeSchroderSeries_eq_one_add_X_mul_largeSchroderSeries_add_X_mul_largeSchroderSeries_sq :
    largeSchroderSeries = 1 + X * largeSchroderSeries + X * largeSchroderSeries ^ 2 := by
  ext n
  by_cases hn : n = 0
  · aesop
  · have hn' : 0 < n := by omega
    simp only [coeff_largeSchroderSeries, map_add, coeff_one, hn, ↓reduceIte, zero_add]
    rw [coeff_X_mul_largeSchroderSeriesSeries_sq _ hn', coeff_X_mul_largeSchroderSeries _ hn',
      show n = n - 1 + 1 by omega, largeSchroder_succ (n - 1)]
    simp only [add_tsub_cancel_right, Nat.add_left_cancel_iff]
    rw [Iic_eq_Icc, Nat.bot_eq_zero, ← range_succ_eq_Icc_zero]

end PowerSeries
