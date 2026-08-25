/-
Copyright (c) 2024 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
module

public import Mathlib.Data.NNReal.Defs

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

@[expose] public section

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
  map_one' := by rw [dite_eq_right one_ne_zero, unzero_coe (x := 1), toAdd_one, zpow_zero]
  map_mul' x y := by
    by_cases hxy : x * y = 0
    · rcases mul_eq_zero.mp hxy with hx | hy
      -- either x = 0 or y = 0
      · rw [dite_eq_left hxy, dite_eq_left hx, zero_mul]
      · rw [dite_eq_left hxy, dite_eq_left hy, mul_zero]
    · obtain ⟨hx, hy⟩ := mul_ne_zero_iff.mp hxy
      -- x ≠ 0 and y ≠ 0
      rw [dite_eq_right hxy, dite_eq_right hx, dite_eq_right hy, ← zpow_add' (Or.inl he),
        ← toAdd_mul]
      congr
      rw [← WithZero.coe_inj, WithZero.coe_mul, coe_unzero hx, coe_unzero hy, coe_unzero hxy]

theorem toNNReal_pos_apply {e : ℝ≥0} (he : e ≠ 0) {x : ℤᵐ⁰} (hx : x = 0) :
    toNNReal he x = 0 := by
  simp [toNNReal, hx]

set_option backward.isDefEq.respectTransparency false in
theorem toNNReal_neg_apply {e : ℝ≥0} (he : e ≠ 0) {x : ℤᵐ⁰} (hx : x ≠ 0) :
    toNNReal he x = e ^ (WithZero.unzero hx).toAdd := by
  simp [toNNReal, hx]

/-- `toNNReal` sends nonzero elements to nonzero elements. -/
theorem toNNReal_ne_zero {e : ℝ≥0} {m : ℤᵐ⁰} (he : e ≠ 0) (hm : m ≠ 0) : toNNReal he m ≠ 0 := by
  simp only [ne_eq, map_eq_zero, hm, not_false_eq_true]

/-- `toNNReal` sends nonzero elements to positive elements. -/
theorem toNNReal_pos {e : ℝ≥0} {m : ℤᵐ⁰} (he : e ≠ 0) (hm : m ≠ 0) : 0 < toNNReal he m :=
  (toNNReal_ne_zero he hm).pos

set_option backward.isDefEq.respectTransparency false in
/-- The map `toNNReal` is strictly monotone whenever `1 < e`. -/
theorem toNNReal_strictMono {e : ℝ≥0} (he : 1 < e) :
    StrictMono (toNNReal he.ne_zero) := by
  intro x y
  cases y
  · simp
  cases x
  · simpa using! zpow_pos he.pos _
  · simp [toNNReal, he]

theorem toNNReal_eq_one_iff {e : ℝ≥0} (m : ℤᵐ⁰) (he0 : e ≠ 0) (he1 : e ≠ 1) :
    toNNReal he0 m = 1 ↔ m = 1 := by
  by_cases hm : m = 0
  · simp only [hm, map_zero, zero_ne_one]
  · refine ⟨fun h1 ↦ ?_, fun h1 ↦ h1 ▸ map_one _⟩
    rw [toNNReal_neg_apply he0 hm, zpow_eq_one_iff_right₀ _root_.zero_le he1, toAdd_eq_zero] at h1
    rw [← WithZero.coe_unzero hm, h1, coe_one]

theorem toNNReal_lt_one_iff {e : ℝ≥0} {m : ℤᵐ⁰} (he : 1 < e) :
    toNNReal (ne_zero_of_lt he) m < 1 ↔ m < 1 := by
  rw [← (toNNReal_strictMono he).lt_iff_lt, map_one]

theorem toNNReal_le_one_iff {e : ℝ≥0} {m : ℤᵐ⁰} (he : 1 < e) :
    toNNReal (ne_zero_of_lt he) m ≤ 1 ↔ m ≤ 1 := by
  rw [← (toNNReal_strictMono he).le_iff_le, map_one]

end WithZeroMulInt
