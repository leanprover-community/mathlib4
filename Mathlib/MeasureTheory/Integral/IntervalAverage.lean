/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Louis (Yiyang) Liu
-/
module

public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Integral average over an interval

In this file we introduce notation `⨍ x in a..b, f x` for the average `⨍ x in Ι a b, f x` of `f`
over the interval `Ι a b = Set.Ioc (min a b) (max a b)` w.r.t. the Lebesgue measure, then prove
formulas for this average:

* `interval_average_eq`: `⨍ x in a..b, f x = (b - a)⁻¹ • ∫ x in a..b, f x`;
* `interval_average_eq_div`: `⨍ x in a..b, f x = (∫ x in a..b, f x) / (b - a)`;
* `exists_eq_interval_average_of_measure`:
    `∃ c ∈ Ι a b, f c = ⨍ x in Ι a b, f x ∂μ`.
* `exists_eq_interval_average_of_noAtoms`:
    `∃ c ∈ uIoo a b, f c = ⨍ x in Ι a b, f x ∂μ`.
* `exists_eq_interval_average`:
    `∃ c ∈ uIoo a b, f c = ⨍ x in a..b, f x`.

We also prove that `⨍ x in a..b, f x = ⨍ x in b..a, f x`, see `interval_average_symm`.

## Notation

`⨍ x in a..b, f x`: average of `f` over the interval `Ι a b` w.r.t. the Lebesgue measure.

-/

public section


open MeasureTheory Set intervalIntegral

open scoped Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `⨍ x in a..b, f x` is the average of `f` over the interval `Ι a b` w.r.t. the Lebesgue
measure. -/
notation3 "⨍ "(...)" in "a".."b",
  "r:60:(scoped f => average (Measure.restrict volume (uIoc a b)) f) => r

theorem interval_average_symm (f : ℝ → E) (a b : ℝ) : (⨍ x in a..b, f x) = ⨍ x in b..a, f x := by
  rw [setAverage_eq, setAverage_eq, uIoc_comm]

theorem interval_average_eq (f : ℝ → E) (a b : ℝ) :
    (⨍ x in a..b, f x) = (b - a)⁻¹ • ∫ x in a..b, f x := by
  rcases le_or_gt a b with h | h
  · rw [setAverage_eq, uIoc_of_le h, Real.volume_real_Ioc_of_le h, integral_of_le h]
  · rw [setAverage_eq, uIoc_of_ge h.le, Real.volume_real_Ioc_of_le h.le, integral_of_ge h.le,
      smul_neg, ← neg_smul, ← inv_neg, neg_sub]

theorem interval_average_eq_div (f : ℝ → ℝ) (a b : ℝ) :
    (⨍ x in a..b, f x) = (∫ x in a..b, f x) / (b - a) := by
  rw [interval_average_eq, smul_eq_mul, div_eq_inv_mul]

/-- Interval averages are invariant when functions change along discrete sets. -/
theorem intervalAverage_congr_codiscreteWithin {a b : ℝ} {f₁ f₂ : ℝ → ℝ}
    (hf : f₁ =ᶠ[Filter.codiscreteWithin (Ι a b)] f₂) :
    ⨍ (x : ℝ) in a..b, f₁ x = ⨍ (x : ℝ) in a..b, f₂ x := by
  rw [interval_average_eq, integral_congr_codiscreteWithin hf, ← interval_average_eq]

variable {f : ℝ → ℝ} {a b : ℝ} {μ : Measure ℝ}

/-- If `f : ℝ → ℝ` is continuous on `uIcc a b`, the interval has finite and nonzero `μ`-measure,
then `∃ c ∈ Ι a b, f c = ⨍ x in Ι a b, f x ∂μ`. -/
theorem exists_eq_interval_average_of_measure
    (hf : ContinuousOn f (uIcc a b)) (hμfin : μ (Ι a b) ≠ ⊤) (hμ0 : μ (Ι a b) ≠ 0) :
    ∃ c ∈ Ι a b, f c = ⨍ x in Ι a b, f x ∂μ :=
  exists_eq_setAverage ⟨nonempty_of_measure_ne_zero hμ0, isPreconnected_Ioc⟩
    (hf.mono uIoc_subset_uIcc) (hf.integrableOn_of_subset_isCompact
    isCompact_uIcc measurableSet_uIoc uIoc_subset_uIcc hμfin) hμfin hμ0

/-- If `f : ℝ → ℝ` is continuous on `uIcc a b`, the interval has finite and nonzero `μ`-measure,
and `μ` has no atoms, then `∃ c ∈ uIoo a b, f c = ⨍ x in Ι a b, f x ∂μ`. -/
theorem exists_eq_interval_average_of_noAtoms
    [NoAtoms μ] (hf : ContinuousOn f (uIcc a b)) (hμfin : μ (Ι a b) ≠ ⊤) (hμ0 : μ (Ι a b) ≠ 0) :
    ∃ c ∈ uIoo a b, f c = ⨍ x in Ι a b, f x ∂μ := by
  have hint : IntegrableOn f (Ι a b) μ := hf.integrableOn_of_subset_isCompact
    isCompact_uIcc measurableSet_uIoc uIoc_subset_uIcc hμfin
  have h : a ≠ b := by intro hab; simp [hab] at hμ0
  let s := uIoo a b
  have hs' : s ⊆ Ι a b := by intro x hx; rcases hx with ⟨h1, h2⟩; grind
  have hs_ev : s =ᵐ[μ] Ι a b := by simpa using Ioo_ae_eq_Ioc
  have hμ0' : μ s ≠ 0 := by
    have hμ : μ s = μ (Ι a b) := by rw [measure_congr hs_ev]
    rwa [hμ]
  obtain ⟨c, hc, heq⟩ := exists_eq_setAverage (isConnected_uIoo h) (hf.mono uIoo_subset_uIcc_self)
    (hint.mono_set hs') (measure_ne_top_of_subset hs' hμfin) hμ0'
  exact ⟨c, hc, by rwa [← setAverage_congr hs_ev]⟩

/-- The mean value theorem for integrals:
There exists a point in an interval such that the mean of a continuous function over the interval
equals the value of the function at the point. -/
theorem exists_eq_interval_average
    (hab : a ≠ b) (hf : ContinuousOn f (uIcc a b)) :
    ∃ c ∈ uIoo a b, f c = ⨍ x in a..b, f x :=
  exists_eq_interval_average_of_noAtoms hf (by simp) (by simpa using sub_ne_zero.mpr hab.symm)
