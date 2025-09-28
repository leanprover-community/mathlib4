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
* `PowerSeries.sum_coeff_X_catalanSeries`: When `n` is a positive integer, the sum of coefficients
  of `X^i * catalan (n - i)` for `0 ≤ i ≤ n` is `catalan (n - 1)`.
* `PowerSeries.coeff_X_mul_catalanSeries`: The coefficient of `X * catalanSeries` at `X^n` is
  `catalan (n - 1)` when `n > 0`.
* `PowerSeries.catalanSeries_one_add_X_mul_self_sq`: The Catalan generating function satisfies the
  equation `catalanSeries = 1 + X * catalanSeries ^ 2`.

## TODO
* Find and prove the closed formula for the Catalan generating function:
  `C(X) = (1 - √(1 - 4X)) / (2X)`

-/

open Finset

namespace PowerSeries

/-- The Catalan generating function as a power series. -/
def catalanSeries : PowerSeries ℕ := PowerSeries.mk catalan

@[simp]
lemma catalanSeries_coeff (n : ℕ) : (coeff n) catalanSeries = catalan n := by
  simp [catalanSeries]

@[simp]
lemma catalanSeries_constantCoeff : constantCoeff catalanSeries = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp only [catalanSeries_coeff, catalan_zero]

theorem sum_coeff_X_catalanSeries (n : ℕ) (hn : 0 < n) :
  ∑ i ∈ range (n + 1), coeff i X * catalan (n - i) =
    catalan (n - 1) := by
  have : ∀ i ∈ range (n + 1), coeff i X * catalan (n - i) =
    if i = 1 then catalan (n - 1) else 0 := by
    intros i hi
    simp_all only [coeff_X, ite_mul, one_mul, zero_mul, mem_range]
  simp_all [sum_congr rfl this, sum_ite_eq', mem_range, lt_add_iff_pos_left]

theorem coeff_X_mul_catalanSeries (n : ℕ) (hn : 0 < n) :
  coeff n (X * catalanSeries) = catalan (n - 1) := by
  simp [coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ
    (fun x y => coeff x X * catalan y)]
  rw [sum_coeff_X_catalanSeries n hn]

theorem catalanSeries_one_add_X_mul_self_sq : catalanSeries = 1 + X * catalanSeries ^ 2 := by
  ext n
  cases n with
  | zero => simp
  | succ n =>
    simp_rw [map_add, coeff_one, if_neg n.succ_ne_zero, zero_add, coeff_succ_X_mul, sq,
      coeff_mul, catalanSeries_coeff, catalan_succ']

end PowerSeries
