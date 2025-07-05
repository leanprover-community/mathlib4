/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Average

/-!
# Integral average over an interval

In this file we introduce notation `⨍ x in a..b, f x` for the average `⨍ x in Ι a b, f x` of `f`
over the interval `Ι a b = Set.Ioc (min a b) (max a b)` w.r.t. the Lebesgue measure, then prove
formulas for this average:

* `interval_average_eq`: `⨍ x in a..b, f x = (b - a)⁻¹ • ∫ x in a..b, f x`;
* `interval_average_eq_div`: `⨍ x in a..b, f x = (∫ x in a..b, f x) / (b - a)`.

We also prove that `⨍ x in a..b, f x = ⨍ x in b..a, f x`, see `interval_average_symm`.

## Notation

`⨍ x in a..b, f x`: average of `f` over the interval `Ι a b` w.r.t. the Lebesgue measure.

-/


open MeasureTheory Set TopologicalSpace

open scoped Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `⨍ x in a..b, f x` is the average of `f` over the interval `Ι a w.r.t. the Lebesgue measure. -/
notation3 "⨍ "(...)" in "a".."b",
  "r:60:(scoped f => average (Measure.restrict volume (uIoc a b)) f) => r

theorem interval_average_symm (f : ℝ → E) (a b : ℝ) : (⨍ x in a..b, f x) = ⨍ x in b..a, f x := by
  rw [setAverage_eq, setAverage_eq, uIoc_comm]

theorem interval_average_eq (f : ℝ → E) (a b : ℝ) :
    (⨍ x in a..b, f x) = (b - a)⁻¹ • ∫ x in a..b, f x := by
  rcases le_or_gt a b with h | h
  · rw [setAverage_eq, uIoc_of_le h, Real.volume_real_Ioc_of_le h,
      intervalIntegral.integral_of_le h]
  · rw [setAverage_eq, uIoc_of_ge h.le, Real.volume_real_Ioc_of_le h.le,
      intervalIntegral.integral_of_ge h.le, smul_neg, ← neg_smul, ← inv_neg, neg_sub]

theorem interval_average_eq_div (f : ℝ → ℝ) (a b : ℝ) :
    (⨍ x in a..b, f x) = (∫ x in a..b, f x) / (b - a) := by
  rw [interval_average_eq, smul_eq_mul, div_eq_inv_mul]

/-- Interval averages are invariant when functions change along discrete sets. -/
theorem intervalAverage_congr_codiscreteWithin {a b : ℝ} {f₁ f₂ : ℝ → ℝ}
    (hf : f₁ =ᶠ[Filter.codiscreteWithin (Ι a b)] f₂) :
    ⨍ (x : ℝ) in a..b, f₁ x = ⨍ (x : ℝ) in a..b, f₂ x := by
  rw [interval_average_eq, intervalIntegral.integral_congr_codiscreteWithin hf,
    ← interval_average_eq]
