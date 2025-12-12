/-
Copyright (c) 2025 Weijie Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weijie Jiang
-/
module

public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Combinatorics.Enumerative.Catalan

/-!
# Catalan Power Series

We introduce the Catalan generating function as a formal power series over `ℕ`:
  `catalanSeries = ∑_{n ≥ 0} catalan n * X^n`

## Main Definitions
* `PowerSeries.catalanSeries`: The Catalan generating function as a power series.

## Main Results
* `PowerSeries.catalanSeries_one_add_X_mul_self_sq`: The Catalan generating function satisfies the
  equation `catalanSeries = 1 + X * catalanSeries ^ 2`.

## TODO
* Find and prove the closed formula for the Catalan generating function:
  `C(X) = (1 - √(1 - 4X)) / (2X)`
-/

@[expose] public section

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

theorem catalanSeries_sq_mul_X_add_one : catalanSeries ^ 2 * X + 1 = catalanSeries := by
  ext n
  cases n with
  | zero => simp
  | succ n =>
    simp_rw [add_comm, map_add, coeff_one, if_neg n.succ_ne_zero, zero_add, coeff_succ_mul_X, sq,
      coeff_mul, catalanSeries_coeff, catalan_succ']

end PowerSeries
