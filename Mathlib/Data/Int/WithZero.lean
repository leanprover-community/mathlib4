/-
Copyright (c) 2024 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
import Mathlib.Data.NNReal.Defs

/-!
# WithZero

In this file we provide some basic API lemmas for the `WithZero` construction and we define
the morphism `WithZeroMultInt.toNNReal`.

## Main Definitions

* `WithZeroMultInt.toNNReal` : The `MonoidWithZeroHom` from `ℤᵐ⁰ → ℝ≥0` sending `0 ↦ 0` and
  `x ↦ e^((WithZero.unzero hx).toAdd)` when `x ≠ 0`, for a nonzero `e : ℝ≥0`.

## Main Results

* `WithZeroMultInt.toNNReal_strictMono` : The map `withZeroMultIntToNNReal` is strictly
  monotone whenever `1 < e`.

## Tags

WithZero, multiplicative, nnreal
-/

assert_not_exists Finset

noncomputable section

open scoped NNReal

open Multiplicative WithZero

namespace WithZeroMulInt

/-- Given a nonzero `e : ℝ≥0`, this is the map `ℤᵐ⁰ → ℝ≥0` sending `0 ↦ 0` and
  `x ↦ e^(WithZero.unzero hx).toAdd` when `x ≠ 0` as a `MonoidWithZeroHom`. -/
def toNNReal {e : ℝ≥0} (he : e ≠ 0) : ℤᵐ⁰ →*₀ ℝ≥0 where
  toFun := fun x ↦ if hx : x = 0 then 0 else e ^ (WithZero.unzero hx).toAdd
  map_zero' := rfl
  map_one' := by
    simp only [dif_neg one_ne_zero]
    erw [toAdd_one, zpow_zero]
  map_mul' x y := by
    by_cases hxy : x * y = 0
    · rcases zero_eq_mul.mp (Eq.symm hxy) with hx | hy
      --either x = 0 or y = 0
      · rw [dif_pos hxy, dif_pos hx, MulZeroClass.zero_mul]
      · rw [dif_pos hxy, dif_pos hy, MulZeroClass.mul_zero]
    · obtain ⟨hx, hy⟩ := mul_ne_zero_iff.mp hxy
      --  x Equiv≠ 0 and y ≠ 0
      rw [dif_neg hxy, dif_neg hx, dif_neg hy, ← zpow_add' (Or.inl he), ← toAdd_mul]
      congr
      rw [← WithZero.coe_inj, WithZero.coe_mul, coe_unzero hx, coe_unzero hy, coe_unzero hxy]

theorem toNNReal_pos_apply {e : ℝ≥0} (he : e ≠ 0) {x : ℤᵐ⁰} (hx : x = 0) :
    toNNReal he x = 0 := by
  simp only [toNNReal, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
  split_ifs; rfl

theorem toNNReal_neg_apply {e : ℝ≥0} (he : e ≠ 0) {x : ℤᵐ⁰} (hx : x ≠ 0) :
    toNNReal he x = e ^ (WithZero.unzero hx).toAdd := by
  simp only [toNNReal, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
  split_ifs
  · tauto
  · rfl

/-- `toNNReal` sends nonzero elements to nonzero elements. -/
theorem toNNReal_ne_zero {e : ℝ≥0} {m : ℤᵐ⁰} (he : e ≠ 0) (hm : m ≠ 0) : toNNReal he m ≠ 0 := by
  simp only [ne_eq, map_eq_zero, hm, not_false_eq_true]

/-- `toNNReal` sends nonzero elements to positive elements. -/
theorem toNNReal_pos {e : ℝ≥0} {m : ℤᵐ⁰} (he : e ≠ 0) (hm : m ≠ 0) : 0 < toNNReal he m :=
  lt_of_le_of_ne zero_le' (toNNReal_ne_zero he hm).symm

/-- The map `toNNReal` is strictly monotone whenever `1 < e`. -/
theorem toNNReal_strictMono {e : ℝ≥0} (he : 1 < e) :
    StrictMono (toNNReal (ne_zero_of_lt he)) := by
  intro x y hxy
  simp only [toNNReal, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
  split_ifs with hx hy hy
  · simp only [hy, not_lt_zero'] at hxy
  · exact zpow_pos he.bot_lt _
  · simp only [hy, not_lt_zero'] at hxy
  · rw [zpow_lt_zpow_iff_right₀ he, Multiplicative.toAdd_lt, ← coe_lt_coe, coe_unzero hx,
      WithZero.coe_unzero hy]
    exact hxy

theorem toNNReal_eq_one_iff {e : ℝ≥0} (m : ℤᵐ⁰) (he0 : e ≠ 0) (he1 : e ≠ 1) :
    toNNReal he0 m = 1 ↔ m = 1 := by
  by_cases hm : m = 0
  · simp only [hm, map_zero, zero_ne_one]
  · refine ⟨fun h1 ↦ ?_, fun h1 ↦ h1 ▸ map_one _⟩
    rw [toNNReal_neg_apply he0 hm, zpow_eq_one_iff_right₀ (zero_le e) he1, toAdd_eq_zero] at h1
    rw [← WithZero.coe_unzero hm, h1, coe_one]

theorem toNNReal_lt_one_iff {e : ℝ≥0} {m : ℤᵐ⁰} (he : 1 < e) :
    toNNReal (ne_zero_of_lt he) m < 1 ↔ m < 1 := by
  rw [← (toNNReal_strictMono he).lt_iff_lt, map_one]

theorem toNNReal_le_one_iff {e : ℝ≥0} {m : ℤᵐ⁰} (he : 1 < e) :
    toNNReal (ne_zero_of_lt he) m ≤ 1 ↔ m ≤ 1 := by
  rw [← (toNNReal_strictMono he).le_iff_le, map_one]

end WithZeroMulInt
