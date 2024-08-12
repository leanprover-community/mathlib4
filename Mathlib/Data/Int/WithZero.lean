/-
Copyright (c) 2024 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
import Mathlib.Data.NNReal.Basic
import Mathlib.RingTheory.Valuation.Basic

/-!
# WithZero

In this file we provide some basic API lemmas for the `WithZero` construction and we define
the morphism `withZeroMultIntToNNReal`.

## Main Definitions

* `withZeroMultIntToNNReal` : The `MonoidWithZeroHom` from `ℤₘ₀ → ℝ≥0` sending `0 ↦ 0` and
  `x ↦ e^(Multiplicative.toAdd (WithZero.unzero hx)` when `x ≠ 0`, for a nonzero `e : ℝ≥0`.

## Main Results

* `withZeroMultIntToNNReal_strictMono` : The map `withZeroMultIntToNNReal` is strictly
   monotone whenever `1 < e`.

## Tags

WithZero, multiplicative, nnreal
-/

noncomputable section

open scoped DiscreteValuation NNReal

open Multiplicative WithZero

/-- Given a nonzero `e : ℝ≥0`, this is the map `ℤₘ₀ → ℝ≥0` sending `0 ↦ 0` and
  `x ↦ e^(Multiplicative.toAdd (WithZero.unzero hx)` when `x ≠ 0` as a `MonoidWithZeroHom`. -/
def withZeroMultIntToNNReal {e : NNReal} (he : e ≠ 0) : ℤₘ₀ →*₀ ℝ≥0 where
  toFun := fun x ↦ if hx : x = 0 then 0 else e ^ Multiplicative.toAdd (WithZero.unzero hx)
  map_zero' := rfl
  map_one' := by
    simp only [dif_neg one_ne_zero]
    erw [toAdd_one, zpow_zero]
  map_mul' x y := by
    simp only
    by_cases hxy : x * y = 0
    · cases' zero_eq_mul.mp (Eq.symm hxy) with hx hy
      --either x = 0 or y = 0
      · rw [dif_pos hxy, dif_pos hx, MulZeroClass.zero_mul]
      · rw [dif_pos hxy, dif_pos hy, MulZeroClass.mul_zero]
    · cases' mul_ne_zero_iff.mp hxy with hx hy
      --  x Equiv≠ 0 and y ≠ 0
      rw [dif_neg hxy, dif_neg hx, dif_neg hy, ← zpow_add' (Or.inl he), ← toAdd_mul]
      congr
      rw [← WithZero.coe_inj, WithZero.coe_mul, coe_unzero hx, coe_unzero hy, coe_unzero hxy]

theorem withZeroMultIntToNNReal_pos_apply {e : NNReal} (he : e ≠ 0) {x : ℤₘ₀} (hx : x = 0) :
    withZeroMultIntToNNReal he x = 0 := by
  simp only [withZeroMultIntToNNReal, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
  split_ifs; rfl

theorem withZeroMultIntToNNReal_neg_apply {e : NNReal} (he : e ≠ 0) {x : ℤₘ₀} (hx : x ≠ 0) :
    withZeroMultIntToNNReal he x = e ^ Multiplicative.toAdd (WithZero.unzero hx) := by
  simp only [withZeroMultIntToNNReal, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
  split_ifs; tauto; rfl

/-- `withZeroMultIntToNNReal` sends nonzero elements to nonzero elements. -/
theorem withZeroMultIntToNNReal_ne_zero {e : NNReal} {m : ℤₘ₀} (he : e ≠ 0) (hm : m ≠ 0) :
    withZeroMultIntToNNReal he m ≠ 0 := by
  simp only [ne_eq, map_eq_zero, hm, not_false_eq_true]

/-- `withZeroMultIntToNNReal` sends nonzero elements to positive elements. -/
theorem withZeroMultIntToNNReal_pos {e : NNReal} {m : ℤₘ₀} (he : e ≠ 0) (hm : m ≠ 0) :
    0 < withZeroMultIntToNNReal he m :=
  lt_of_le_of_ne zero_le' (withZeroMultIntToNNReal_ne_zero he hm).symm

-- [Mathlib.Data.NNReal.Basic]
/-- The map `withZeroMultIntToNNReal` is strictly monotone whenever `1 < e`. -/
theorem withZeroMultIntToNNReal_strictMono {e : NNReal} (he : 1 < e) :
    StrictMono (withZeroMultIntToNNReal (ne_zero_of_lt he)) := by
  intro x y hxy
  simp only [withZeroMultIntToNNReal, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
  split_ifs with hx hy hy
  · simp only [hy, not_lt_zero'] at hxy
  · exact NNReal.zpow_pos (ne_zero_of_lt he) _
  · simp only [hy, not_lt_zero'] at hxy
  · rw [zpow_lt_iff_lt he, Multiplicative.toAdd_lt, ← WithZero.coe_lt_coe, WithZero.coe_unzero hx,
      WithZero.coe_unzero hy]
    exact hxy
