/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Data.Complex.Module

/-!
# The partial order on the complex numbers

This order is defined by `z ≤ w ↔ z.re ≤ w.re ∧ z.im = w.im`.

This is a natural order on `ℂ` because, as is well-known, there does not exist an order on `ℂ`
making it into a `LinearOrderedField`. However, the order described above is the canonical order
stemming from the structure of `ℂ` as a ⋆-ring (i.e., it becomes a `StarOrderedRing`). Moreover,
with this order `ℂ` is a `StrictOrderedCommRing` and the coercion `(↑) : ℝ → ℂ` is an order
embedding.

This file only provides `Complex.partialOrder` and lemmas about it. Further structural classes are
provided by `Mathlib/Data/IsROrC/Basic.lean` as

* `IsROrC.toStrictOrderedCommRing`
* `IsROrC.toStarOrderedRing`
* `IsROrC.toOrderedSMul`

These are all only available with `open scoped ComplexOrder`.
-/

namespace Complex

/-- We put a partial order on ℂ so that `z ≤ w` exactly if `w - z` is real and nonnegative.
Complex numbers with different imaginary parts are incomparable.
-/
protected def partialOrder : PartialOrder ℂ where
  le z w := z.re ≤ w.re ∧ z.im = w.im
  lt z w := z.re < w.re ∧ z.im = w.im
  lt_iff_le_not_le z w := by
    dsimp
    -- ⊢ z.re < w.re ∧ z.im = w.im ↔ (z.re ≤ w.re ∧ z.im = w.im) ∧ ¬(w.re ≤ z.re ∧ w. …
    rw [lt_iff_le_not_le]
    -- ⊢ (z.re ≤ w.re ∧ ¬w.re ≤ z.re) ∧ z.im = w.im ↔ (z.re ≤ w.re ∧ z.im = w.im) ∧ ¬ …
    tauto
    -- 🎉 no goals
  le_refl x := ⟨le_rfl, rfl⟩
  le_trans x y z h₁ h₂ := ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩
  le_antisymm z w h₁ h₂ := ext (h₁.1.antisymm h₂.1) h₁.2
#align complex.partial_order Complex.partialOrder

namespace _root_.ComplexOrder

-- Porting note: made section into namespace to allow scoping
scoped[ComplexOrder] attribute [instance] Complex.partialOrder

end _root_.ComplexOrder

open ComplexOrder

theorem le_def {z w : ℂ} : z ≤ w ↔ z.re ≤ w.re ∧ z.im = w.im :=
  Iff.rfl
#align complex.le_def Complex.le_def

theorem lt_def {z w : ℂ} : z < w ↔ z.re < w.re ∧ z.im = w.im :=
  Iff.rfl
#align complex.lt_def Complex.lt_def


@[simp, norm_cast]
theorem real_le_real {x y : ℝ} : (x : ℂ) ≤ (y : ℂ) ↔ x ≤ y := by simp [le_def, ofReal']
                                                                 -- 🎉 no goals
#align complex.real_le_real Complex.real_le_real

@[simp, norm_cast]
theorem real_lt_real {x y : ℝ} : (x : ℂ) < (y : ℂ) ↔ x < y := by simp [lt_def, ofReal']
                                                                 -- 🎉 no goals
#align complex.real_lt_real Complex.real_lt_real


@[simp, norm_cast]
theorem zero_le_real {x : ℝ} : (0 : ℂ) ≤ (x : ℂ) ↔ 0 ≤ x :=
  real_le_real
#align complex.zero_le_real Complex.zero_le_real

@[simp, norm_cast]
theorem zero_lt_real {x : ℝ} : (0 : ℂ) < (x : ℂ) ↔ 0 < x :=
  real_lt_real
#align complex.zero_lt_real Complex.zero_lt_real

theorem not_le_iff {z w : ℂ} : ¬z ≤ w ↔ w.re < z.re ∨ z.im ≠ w.im := by
  rw [le_def, not_and_or, not_le]
  -- 🎉 no goals
#align complex.not_le_iff Complex.not_le_iff

theorem not_lt_iff {z w : ℂ} : ¬z < w ↔ w.re ≤ z.re ∨ z.im ≠ w.im := by
  rw [lt_def, not_and_or, not_lt]
  -- 🎉 no goals
#align complex.not_lt_iff Complex.not_lt_iff

theorem not_le_zero_iff {z : ℂ} : ¬z ≤ 0 ↔ 0 < z.re ∨ z.im ≠ 0 :=
  not_le_iff
#align complex.not_le_zero_iff Complex.not_le_zero_iff

theorem not_lt_zero_iff {z : ℂ} : ¬z < 0 ↔ 0 ≤ z.re ∨ z.im ≠ 0 :=
  not_lt_iff
#align complex.not_lt_zero_iff Complex.not_lt_zero_iff

theorem eq_re_ofReal_le {r : ℝ} {z : ℂ} (hz : (r : ℂ) ≤ z) : z = z.re := by
  ext
  -- ⊢ z.re = (↑z.re).re
  rfl
  -- ⊢ z.im = (↑z.re).im
  simp only [← (Complex.le_def.1 hz).2, Complex.zero_im, Complex.ofReal_im]
  -- 🎉 no goals
#align complex.eq_re_of_real_le Complex.eq_re_ofReal_le

end Complex
