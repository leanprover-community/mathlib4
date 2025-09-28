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
* `interval_average_eq_div`: `⨍ x in a..b, f x = (∫ x in a..b, f x) / (b - a)`;
* `exists_eq_interval_average`: `∃ c, f c = ⨍ (x : ℝ) in a..b, f x`.

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

/-- The mean value theorem for integrals:
There exists a point in an interval such that the mean of a continuous function over the interval
equals the value of the function at the point. -/
theorem exists_eq_interval_average
    {f : ℝ → ℝ} {a b : ℝ} (hab : a ≠ b) (hf : ContinuousOn f (uIcc a b)) :
    ∃ c ∈ uIoo a b, f c = ⨍ (x : ℝ) in a..b, f x := by
  wlog h : a < b generalizing a b
  · rw [uIcc_comm] at hf
    have := this hab.symm hf (lt_of_le_of_ne (le_of_not_gt h) (Ne.symm hab))
    rwa [uIoo_comm, interval_average_symm] at this
  let ave := ⨍ (x : ℝ) in a..b, f x
  have h_vol_fin1 : volume (uIoc a b) ≠ 0 := by simpa [h.le] using h
  have h_vol_fin2 : volume (uIoc a b) ≠ ⊤ := by simp [h.le]
  have h_intble : IntegrableOn f (uIoc a b) := by
    have : IntegrableOn f (uIcc a b) := hf.integrableOn_uIcc
    rwa [uIcc_of_lt h,integrableOn_Icc_iff_integrableOn_Ioc, ←uIoc_of_le (le_of_lt h)] at this
  let S1 := {x | x ∈ uIoc a b ∧ f x ≤ ave}
  let S2 := {x | x ∈ uIoc a b ∧ ave ≤ f x}
  have h_meas1 : volume (S1 \ {b}) ≠ 0 := by
    rw [measure_diff_null Real.volume_singleton]
    exact (measure_le_setAverage_pos h_vol_fin1 h_vol_fin2 h_intble).ne'
  have h_meas2 : volume (S2 \ {b}) ≠ 0 := by
    rw [measure_diff_null Real.volume_singleton]
    exact (measure_setAverage_le_pos h_vol_fin1 h_vol_fin2 h_intble).ne'
  obtain ⟨c1, ⟨hc1_mem, hc1_le⟩, hc1'⟩ := nonempty_of_measure_ne_zero h_meas1
  have hc1' : c1 ∈ Ioo a b := by
    rw [Set.uIoc_of_le (le_of_lt h)] at hc1_mem
    rw [notMem_singleton_iff] at hc1'
    exact ⟨hc1_mem.1, lt_of_le_of_ne hc1_mem.2 hc1'⟩
  obtain ⟨c2, ⟨hc2_mem, hc2_ge⟩, hc2'⟩ := nonempty_of_measure_ne_zero h_meas2
  have hc2' : c2 ∈ Ioo a b := by
    rw [Set.uIoc_of_le (le_of_lt h)] at hc2_mem
    rw [notMem_singleton_iff] at hc2'
    exact ⟨hc2_mem.1, lt_of_le_of_ne hc2_mem.2 hc2'⟩
  have h_interval : uIcc c1 c2 ⊆ uIoo a b := by
    rw [uIoo_of_lt h]
    intro x hx
    rw [mem_uIcc] at hx
    simp only [mem_Ioo]
    rcases hx with h1 | h2
    · exact ⟨lt_of_lt_of_le hc1'.1 h1.1, lt_of_le_of_lt h1.2 hc2'.2⟩
    · exact ⟨lt_of_lt_of_le hc2'.1 h2.1, lt_of_le_of_lt h2.2 hc1'.2⟩
  have h_interval' : uIcc c1 c2 ⊆ uIcc a b := fun x hx => Ioo_subset_Icc_self (h_interval hx)
  have h_ave : ave ∈ Icc (f c1) (f c2) := ⟨hc1_le,hc2_ge⟩
  have h_image := intermediate_value_uIcc (hf.mono h_interval') (Icc_subset_uIcc h_ave)
  exact ((mem_image f (uIcc c1 c2) ave).mp (h_image)).imp (fun c hc => ⟨h_interval hc.1, hc.2⟩)
