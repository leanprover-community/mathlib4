/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Data.ENNReal.Operations
public import Mathlib.Data.ENNReal.Real

/-!
# Symmetric absolute difference for `ℝ≥0∞`

This file defines `ENNReal.absDiff`, a symmetric absolute difference on extended nonnegative reals
using truncated subtraction, and proves its basic algebraic properties.

## Main definitions

- `ENNReal.absDiff a b`: the symmetric absolute difference `(a - b) + (b - a)` in `ℝ≥0∞`

## Main results

- `ENNReal.absDiff_toReal`: when both arguments are finite,
  `(absDiff a b).toReal = |a.toReal - b.toReal|`
- `ENNReal.absDiff_triangle`: the triangle inequality
- `ENNReal.absDiff_eq_zero`: `absDiff a b = 0 ↔ a = b`
- `ENNReal.absDiff_tsub_tsub`: `absDiff (c - a) (c - b) = absDiff a b` under suitable hypotheses
- `ENNReal.absDiff_mul_right_le`: `absDiff (a * c) (b * c) ≤ absDiff a b * c`

## Tags

ENNReal, absolute difference, symmetric difference, truncated subtraction
-/

@[expose] public section

namespace ENNReal

/-- Symmetric absolute difference in `ℝ≥0∞`, defined as `(a - b) + (b - a)`.
Satisfies `(absDiff a b).toReal = |a.toReal - b.toReal|` when both arguments are finite. -/
protected noncomputable def absDiff (a b : ℝ≥0∞) : ℝ≥0∞ := (a - b) + (b - a)

@[simp]
lemma absDiff_self (a : ℝ≥0∞) : ENNReal.absDiff a a = 0 := by
  simp [ENNReal.absDiff]

/-- `ENNReal.absDiff` is symmetric. -/
lemma absDiff_comm (a b : ℝ≥0∞) : ENNReal.absDiff a b = ENNReal.absDiff b a := by
  simp [ENNReal.absDiff, add_comm]

/-- `ENNReal.absDiff a b ≤ a + b`. -/
lemma absDiff_le_add (a b : ℝ≥0∞) : ENNReal.absDiff a b ≤ a + b :=
  add_le_add tsub_le_self tsub_le_self

/-- `a - c ≤ (a - b) + (b - c)` for truncated subtraction. -/
lemma tsub_le_tsub_add_tsub (a b c : ℝ≥0∞) : a - c ≤ (a - b) + (b - c) := by
  rw [tsub_le_iff_right]
  calc a ≤ (a - b) + b := le_tsub_add
    _ ≤ (a - b) + ((b - c) + c) := by gcongr; exact le_tsub_add
    _ = ((a - b) + (b - c)) + c := (add_assoc _ _ _).symm

/-- Triangle inequality for `ENNReal.absDiff`. -/
lemma absDiff_triangle (a b c : ℝ≥0∞) :
    ENNReal.absDiff a c ≤ ENNReal.absDiff a b + ENNReal.absDiff b c := by
  unfold ENNReal.absDiff
  calc (a - c) + (c - a)
      ≤ ((a - b) + (b - c)) + ((c - b) + (b - a)) :=
        add_le_add (tsub_le_tsub_add_tsub a b c)
          (tsub_le_tsub_add_tsub c b a)
    _ = ((a - b) + (b - a)) + ((b - c) + (c - b)) := by ring

/-- Connection between `ENNReal.absDiff` and real-valued absolute difference. -/
lemma absDiff_toReal {a b : ℝ≥0∞} (ha : a ≠ ⊤) (hb : b ≠ ⊤) :
    (ENNReal.absDiff a b).toReal = |a.toReal - b.toReal| := by
  rcases le_total a b with hab | hab
  · have h1 : a - b = 0 := tsub_eq_zero_of_le hab
    have h2 : a.toReal ≤ b.toReal := (toReal_le_toReal ha hb).mpr hab
    simp only [ENNReal.absDiff, h1, zero_add,
      abs_of_nonpos (sub_nonpos.mpr h2), neg_sub]
    exact toReal_sub_of_le hab hb
  · have h1 : b - a = 0 := tsub_eq_zero_of_le hab
    have h2 : b.toReal ≤ a.toReal := (toReal_le_toReal hb ha).mpr hab
    simp only [ENNReal.absDiff, h1, add_zero,
      abs_of_nonneg (sub_nonneg.mpr h2)]
    exact toReal_sub_of_le hab ha

/-- `absDiff` commutes with complementary subtraction from a common value. -/
lemma absDiff_tsub_tsub {a b c : ℝ≥0∞} (ha : a ≤ c) (hb : b ≤ c)
    (hc : c ≠ ⊤) :
    ENNReal.absDiff (c - a) (c - b) = ENNReal.absDiff a b := by
  have hca_ne : c - a ≠ ⊤ := ne_top_of_le_ne_top hc tsub_le_self
  have hcb_ne : c - b ≠ ⊤ := ne_top_of_le_ne_top hc tsub_le_self
  rcases le_total a b with hab | hab
  · have hcb_le_ca : c - b ≤ c - a := tsub_le_tsub_left hab c
    simp only [ENNReal.absDiff, tsub_eq_zero_of_le hab,
      tsub_eq_zero_of_le hcb_le_ca, add_zero, zero_add]
    rw [show c - a = (c - b) + (b - a) from
      (tsub_add_tsub_cancel hb hab).symm]
    exact ENNReal.add_sub_cancel_left hcb_ne
  · have hca_le_cb : c - a ≤ c - b := tsub_le_tsub_left hab c
    simp only [ENNReal.absDiff, tsub_eq_zero_of_le hab,
      tsub_eq_zero_of_le hca_le_cb, add_zero, zero_add]
    rw [show c - b = (c - a) + (a - b) from
      (tsub_add_tsub_cancel ha hab).symm]
    exact ENNReal.add_sub_cancel_left hca_ne

@[simp]
lemma absDiff_eq_zero {a b : ℝ≥0∞} : ENNReal.absDiff a b = 0 ↔ a = b := by
  constructor
  · intro h
    have h1 : a - b = 0 := by exact_mod_cast (add_eq_zero.mp h).1
    have h2 : b - a = 0 := by exact_mod_cast (add_eq_zero.mp h).2
    exact le_antisymm (tsub_eq_zero_iff_le.mp h1)
      (tsub_eq_zero_iff_le.mp h2)
  · rintro rfl; exact absDiff_self _

/-- `a * c - b * c ≤ (a - b) * c` for truncated subtraction. -/
lemma tsub_mul_le (a b c : ℝ≥0∞) : a * c - b * c ≤ (a - b) * c := by
  rw [tsub_le_iff_right]
  calc a * c ≤ ((a - b) + b) * c := by gcongr; exact le_tsub_add
    _ = (a - b) * c + b * c := add_mul _ _ _

/-- Scaling inequality: `absDiff (a * c) (b * c) ≤ absDiff a b * c`. -/
lemma absDiff_mul_right_le (a b c : ℝ≥0∞) :
    ENNReal.absDiff (a * c) (b * c) ≤ ENNReal.absDiff a b * c := by
  simp only [ENNReal.absDiff]
  calc a * c - b * c + (b * c - a * c)
      ≤ (a - b) * c + (b - a) * c :=
        add_le_add (tsub_mul_le a b c) (tsub_mul_le b a c)
    _ = ((a - b) + (b - a)) * c := (add_mul _ _ _).symm

end ENNReal
