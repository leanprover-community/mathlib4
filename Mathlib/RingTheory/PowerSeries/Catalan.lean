/-
Copyright (c) 2025 Weijie Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weijie Jiang
-/
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Combinatorics.Enumerative.Catalan

/-!
# Catalan Power Series
We introduce the Catalan generating function as a formal power series over `ℕ`:
  `catalanSeries = ∑_{n ≥ 0} catalan n * X^n`

## Main Definitions
* `PowerSeries.catalanSeries`: The Catalan generating function as a power series.

## Main Results
* `PowerSeries.sum_coeff_X_catalanSeries`: When `n` is a natural number,
  each term in the sum `coeff i X * catalan (n - i)` is 0 except for `i = 1`.
* `PowerSeries.coeff_X_mul_catalanSeries`: The coefficient of `X * catalanSeries` at `X^n` is
  `catalan (n - 1)` when `n > 0`/
* `PowerSeries.catalanSeries_one_add_X_mul_self_sq`: The Catalan generating function satisfies the
  equation `catalanSeries = 1 + X * catalanSeries ^ 2`.

## TODO
* Find and prove the closed formula for the Catalan generating function:
  `C(X) = (1 - √(1 - 4X)) / (2X)`

-/

open Finset

namespace PowerSeries

def catalanSeries : PowerSeries ℕ := PowerSeries.mk catalan

@[simp]
lemma catalanSeries_coeff (n : ℕ) : (coeff n) catalanSeries = catalan n := by
  simp [catalanSeries]

@[simp]
lemma catalanSeries_constantCoeff : constantCoeff catalanSeries = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp only [catalanSeries_coeff, catalan_zero]

theorem sum_coeff_X_catalanSeries (n : ℕ) :
  ∀ i ∈ range (n + 1), coeff i X * catalan (n - i) =
    if i = 1 then catalan (n - 1) else 0 := by
  intros i hi
  simp_all only [coeff_X, ite_mul, one_mul, zero_mul, mem_range]

theorem coeff_X_mul_catalanSeries (n : ℕ) (hn : 0 < n) :
  coeff n (X * catalanSeries) = catalan (n - 1) := by
  simp [coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ
    (fun x y => coeff x X * catalan y)]
  rw [Finset.sum_congr rfl (sum_coeff_X_catalanSeries n)]
  simp_all only [sum_ite_eq', mem_range, lt_add_iff_pos_left, ↓reduceIte]

theorem catalanSeries_one_add_X_mul_self_sq : catalanSeries = 1 + X * catalanSeries ^ 2 := by
  rw [pow_two, ← mul_assoc]
  ext n
  by_cases hn : n = 0
  · aesop
  · have hn' : 0 < n := by omega
    simp [catalanSeries_coeff, hn]
    rw [coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ
      (fun x y => coeff x (X * catalanSeries) * coeff y catalanSeries), Nat.succ_eq_add_one]
    rw [sum_range_eq_add_Ico _ (by omega)]
    simp
    by_cases hn1 : n = 1
    · simp [hn1, catalan_one, catalanSeries_coeff]
    · have hn1' : 1 < n := by omega
      have : ∑ x ∈ Ico 1 (n + 1), (coeff x) (X * catalanSeries) * catalan (n - x) =
        ∑ x ∈ Ico 1 (n + 1), catalan (x - 1) * catalan (n - x) := by
        apply sum_congr rfl
        intros x hx
        simp at hx
        rw [coeff_X_mul_catalanSeries x (by omega)]
      rw [this, sum_Ico_eq_sum_range]
      simp only [add_tsub_cancel_right, add_tsub_cancel_left]
      rw [show n = n - 1 + 1 by omega, catalan_succ' (n - 1), Nat.sum_antidiagonal_eq_sum_range_succ
        (fun x y => catalan x * catalan y), Nat.succ_eq_add_one, show n - 1 + 1 = n by omega]
      simp_rw [show ∀ x, n - 1 - x = n - (1 + x) by omega]

end PowerSeries
