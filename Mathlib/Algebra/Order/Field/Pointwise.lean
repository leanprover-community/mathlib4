/-
Copyright (c) 2021 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best, Yaël Dillies
-/
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Algebra.Order.Field.Defs
import Mathlib.Algebra.SMulWithZero

/-!
# Pointwise operations on ordered algebraic objects

This file contains lemmas about the effect of pointwise operations on sets with an order structure.
-/

open Function Set
open scoped Pointwise

namespace LinearOrderedField

variable {K : Type*} [LinearOrderedField K] {a b r : K} (hr : 0 < r)
include hr

theorem smul_Ioo : r • Ioo a b = Ioo (r • a) (r • b) := by
  ext x
  simp only [mem_smul_set, smul_eq_mul, mem_Ioo]
  constructor
  · rintro ⟨a, ⟨a_h_left_left, a_h_left_right⟩, rfl⟩
    constructor
    · exact (mul_lt_mul_left hr).mpr a_h_left_left
    · exact (mul_lt_mul_left hr).mpr a_h_left_right
  · rintro ⟨a_left, a_right⟩
    use x / r
    refine ⟨⟨(lt_div_iff₀' hr).mpr a_left, (div_lt_iff₀' hr).mpr a_right⟩, ?_⟩
    rw [mul_div_cancel₀ _ (ne_of_gt hr)]

theorem smul_Icc : r • Icc a b = Icc (r • a) (r • b) := by
  ext x
  simp only [mem_smul_set, smul_eq_mul, mem_Icc]
  constructor
  · rintro ⟨a, ⟨a_h_left_left, a_h_left_right⟩, rfl⟩
    constructor
    · exact (mul_le_mul_left hr).mpr a_h_left_left
    · exact (mul_le_mul_left hr).mpr a_h_left_right
  · rintro ⟨a_left, a_right⟩
    use x / r
    refine ⟨⟨(le_div_iff₀' hr).mpr a_left, (div_le_iff₀' hr).mpr a_right⟩, ?_⟩
    rw [mul_div_cancel₀ _ (ne_of_gt hr)]

theorem smul_Ico : r • Ico a b = Ico (r • a) (r • b) := by
  ext x
  simp only [mem_smul_set, smul_eq_mul, mem_Ico]
  constructor
  · rintro ⟨a, ⟨a_h_left_left, a_h_left_right⟩, rfl⟩
    constructor
    · exact (mul_le_mul_left hr).mpr a_h_left_left
    · exact (mul_lt_mul_left hr).mpr a_h_left_right
  · rintro ⟨a_left, a_right⟩
    use x / r
    refine ⟨⟨(le_div_iff₀' hr).mpr a_left, (div_lt_iff₀' hr).mpr a_right⟩, ?_⟩
    rw [mul_div_cancel₀ _ (ne_of_gt hr)]

theorem smul_Ioc : r • Ioc a b = Ioc (r • a) (r • b) := by
  ext x
  simp only [mem_smul_set, smul_eq_mul, mem_Ioc]
  constructor
  · rintro ⟨a, ⟨a_h_left_left, a_h_left_right⟩, rfl⟩
    constructor
    · exact (mul_lt_mul_left hr).mpr a_h_left_left
    · exact (mul_le_mul_left hr).mpr a_h_left_right
  · rintro ⟨a_left, a_right⟩
    use x / r
    refine ⟨⟨(lt_div_iff₀' hr).mpr a_left, (div_le_iff₀' hr).mpr a_right⟩, ?_⟩
    rw [mul_div_cancel₀ _ (ne_of_gt hr)]

theorem smul_Ioi : r • Ioi a = Ioi (r • a) := by
  ext x
  simp only [mem_smul_set, smul_eq_mul, mem_Ioi]
  constructor
  · rintro ⟨a_w, a_h_left, rfl⟩
    exact (mul_lt_mul_left hr).mpr a_h_left
  · rintro h
    use x / r
    constructor
    · exact (lt_div_iff₀' hr).mpr h
    · exact mul_div_cancel₀ _ (ne_of_gt hr)

theorem smul_Iio : r • Iio a = Iio (r • a) := by
  ext x
  simp only [mem_smul_set, smul_eq_mul, mem_Iio]
  constructor
  · rintro ⟨a_w, a_h_left, rfl⟩
    exact (mul_lt_mul_left hr).mpr a_h_left
  · rintro h
    use x / r
    constructor
    · exact (div_lt_iff₀' hr).mpr h
    · exact mul_div_cancel₀ _ (ne_of_gt hr)

theorem smul_Ici : r • Ici a = Ici (r • a) := by
  ext x
  simp only [mem_smul_set, smul_eq_mul, mem_Ioi]
  constructor
  · rintro ⟨a_w, a_h_left, rfl⟩
    exact (mul_le_mul_left hr).mpr a_h_left
  · rintro h
    use x / r
    constructor
    · exact (le_div_iff₀' hr).mpr h
    · exact mul_div_cancel₀ _ (ne_of_gt hr)

theorem smul_Iic : r • Iic a = Iic (r • a) := by
  ext x
  simp only [mem_smul_set, smul_eq_mul, mem_Iio]
  constructor
  · rintro ⟨a_w, a_h_left, rfl⟩
    exact (mul_le_mul_left hr).mpr a_h_left
  · rintro h
    use x / r
    constructor
    · exact (div_le_iff₀' hr).mpr h
    · exact mul_div_cancel₀ _ (ne_of_gt hr)

end LinearOrderedField
