/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Louis (Yiyang) Liu
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.Average

/-!
# Integral average over an interval

In this file we introduce notation `⨍ x in a..b, f x` for the average `⨍ x in Ι a b, f x` of `f`
over the interval `Ι a b = Set.Ioc (min a b) (max a b)` w.r.t. the Lebesgue measure, then prove
formulas for this average:

* `interval_average_eq`: `⨍ x in a..b, f x = (b - a)⁻¹ • ∫ x in a..b, f x`;
* `interval_average_eq_div`: `⨍ x in a..b, f x = (∫ x in a..b, f x) / (b - a)`;
* `exists_eq_interval_average_of_measure`: `∃ c, f c = ⨍ x in (uIoc a b), f x ∂μ`.
* `exists_eq_interval_average_of_NoAtoms`: `∃ c, f c = ⨍ x in (uIoc a b), f x ∂μ`.
* `exists_eq_interval_average`: `∃ c, f c = ⨍ (x : ℝ) in a..b, f x`.

We also prove that `⨍ x in a..b, f x = ⨍ x in b..a, f x`, see `interval_average_symm`.

## Notation

`⨍ x in a..b, f x`: average of `f` over the interval `Ι a b` w.r.t. the Lebesgue measure.

-/

@[expose] public section


open MeasureTheory Set TopologicalSpace

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

/-- If `f : ℝ → ℝ` is continuous on `uIcc a b`, the interval has finite and nonzero `μ`-measure,
then there exists `c ∈ uIcc a b` such that 
`f c = ⨍ x in (uIoc a b), f x ∂μ`. -/
theorem exists_eq_interval_average_of_measure
    {f : ℝ → ℝ} {a b : ℝ} {μ : Measure ℝ}
    (hf : ContinuousOn f (uIcc a b))
    (hμfin : μ (uIoc a b) ≠ ⊤)
    (hμ0 : μ (uIoc a b) ≠ 0) :
    ∃ c ∈ uIcc a b, f c = ⨍ x in (uIoc a b), f x ∂μ := by
  wlog h : a ≤ b generalizing a b
  · simp at h
    specialize this
      (a := b) (b := a) (by rwa [uIcc_comm])
      (by rwa [uIoc_comm]) (by rwa [uIoc_comm])
      (h.le)
    rcases this with ⟨c, hc, hEq⟩
    refine ⟨c, by rwa [uIcc_comm], by rwa [uIoc_comm]⟩
  let ave := average (μ.restrict (uIoc a b)) f
  let S₁ := {x | x ∈ uIoc a b ∧ f x ≤ ave}
  let S₂ := {x | x ∈ uIoc a b ∧ ave ≤ f x}
  have hint : IntegrableOn f (uIoc a b) μ := by
    have hsubset : uIoc a b ⊆ uIcc a b := uIoc_subset_uIcc
    have hcomp : IsCompact (uIcc a b) := isCompact_uIcc
    obtain ⟨c, hc, hmax⟩ := hcomp.exists_isMaxOn nonempty_uIcc (hf.norm)
    apply IntegrableOn.of_bound ?_ ?_ (|f c|) ?_
    · rwa [lt_top_iff_ne_top]
    · apply ContinuousOn.aestronglyMeasurable
      · exact ContinuousOn.mono hf hsubset
      · exact measurableSet_uIoc
    · rw [ae_restrict_iff' measurableSet_uIoc]
      apply ae_of_all
      intro m hm
      apply hmax
      exact hsubset hm
  have hS₁ : 0 < μ S₁ := measure_le_setAverage_pos hμ0 hμfin hint
  have hS₂ : 0 < μ S₂ := measure_setAverage_le_pos hμ0 hμfin hint
  have hS₁nonempty : S₁.Nonempty := nonempty_of_measure_ne_zero hS₁.ne'
  have hS₂nonempty : S₂.Nonempty := nonempty_of_measure_ne_zero hS₂.ne'
  rw [nonempty_def] at *
  rcases hS₁nonempty with ⟨c₁, hc₁⟩
  rcases hS₂nonempty with ⟨c₂, hc₂⟩
  have hc₁Ioc : c₁ ∈ Ioc a b := by
    simpa [h] using hc₁.1
  have hc₂Ioc : c₂ ∈ Ioc a b := by
    simpa [h] using hc₂.1
  have h_subset : uIcc c₁ c₂ ⊆ Icc a b := by
    intro x hx
    rw [mem_uIcc] at hx
    grind
  have h_ivt : ∃ c ∈ uIcc c₁ c₂, f c = ave := by
    apply intermediate_value_uIcc
    · refine ContinuousOn.mono hf ?_
      rwa [uIcc_of_le h]
    · rw [mem_uIcc]
      grind
  rcases h_ivt with ⟨c, hc_mem, hfc⟩
  refine ⟨c, ?_, hfc⟩
  rw [mem_uIcc]
  grind

/-- If `f : ℝ → ℝ` is continuous on `uIcc a b`, the interval has finite and nonzero `μ`-measure,
and `μ` has no atoms, then there exists `c ∈ uIoo a b` such that 
`f c = ⨍ x in (uIoc a b), f x ∂μ`. -/
theorem exists_eq_interval_average_of_NoAtoms
    {f : ℝ → ℝ} {a b : ℝ}
    {μ : Measure ℝ} [NoAtoms μ]
    (hf : ContinuousOn f (uIcc a b))
    (hμfin : μ (uIoc a b) ≠ ⊤)
    (hμ0 : μ (uIoc a b) ≠ 0) :
    ∃ c ∈ uIoo a b, f c = ⨍ x in (uIoc a b), f x ∂μ := by
  wlog h : a ≤ b generalizing a b
  · simp at h
    specialize this
      (a := b) (b := a) (by rwa [uIcc_comm])
      (by rwa [uIoc_comm]) (by rwa [uIoc_comm]) (h.le)
    rcases this with ⟨c, hc, hEq⟩
    refine ⟨c, ?_, ?_⟩
    · simpa [uIoo_comm] using hc
    · have hswap : Ι a b = Ι b a := uIoc_comm a b
      rwa [hswap]
  let ave := average (μ.restrict (uIoc a b)) f
  let S₁ := {x | x ∈ uIoc a b ∧ f x ≤ ave}
  let S₂ := {x | x ∈ uIoc a b ∧ ave ≤ f x}
  have hint : IntegrableOn f (uIoc a b) μ := by
    have hsubset : uIoc a b ⊆ uIcc a b := uIoc_subset_uIcc
    have hcomp : IsCompact (uIcc a b) := isCompact_uIcc
    obtain ⟨c, hc, hmax⟩ := hcomp.exists_isMaxOn nonempty_uIcc hf.norm
    apply IntegrableOn.of_bound ?_ ?_ (|f c|) ?_
    · rwa [lt_top_iff_ne_top]
    · apply ContinuousOn.aestronglyMeasurable
      · exact ContinuousOn.mono hf hsubset
      · exact measurableSet_uIoc
    · rw [ae_restrict_iff' measurableSet_uIoc]
      apply ae_of_all
      intro m hm
      apply hmax
      exact hsubset hm
  have hS₁ : 0 < μ S₁ := measure_le_setAverage_pos hμ0 hμfin hint
  have hS₂ : 0 < μ S₂ := measure_setAverage_le_pos hμ0 hμfin hint
  have hb0 : μ {b} = 0 := measure_singleton b
  have hS₁pos' : 0 < μ (S₁ \ {b}) := by
    have hcap0 : μ (S₁ ∩ {b}) = 0 := measure_inter_null_of_null_right S₁ hb0
    have : μ (S₁ \ {b}) = μ S₁ := AEDisjoint.measure_diff_left hcap0
    grind
  have hS₂pos' : 0 < μ (S₂ \ {b}) := by
    have hcap0 : μ (S₂ ∩ {b}) = 0 := measure_inter_null_of_null_right S₂ hb0
    have : μ (S₂ \ {b}) = μ S₂ := AEDisjoint.measure_diff_left hcap0
    grind
  have hS₁nonempty : (S₁ \ {b}).Nonempty := nonempty_of_measure_ne_zero hS₁pos'.ne'
  have hS₂nonempty : (S₂ \ {b}).Nonempty := nonempty_of_measure_ne_zero hS₂pos'.ne'
  rcases hS₁nonempty with ⟨c₁, hc₁⟩
  rcases hS₂nonempty with ⟨c₂, hc₂⟩
  have hc₁Ioc : c₁ ∈ Ioc a b := by
    simpa [h] using (hc₁.1 : c₁ ∈ S₁).1
  have hc₂Ioc : c₂ ∈ Ioc a b := by
    simpa [h] using (hc₂.1 : c₂ ∈ S₂).1
  have h_subset : uIcc c₁ c₂ ⊆ Icc a b := by
    intro x hx
    rw [mem_uIcc] at hx
    grind
  have h_ivt : ∃ c ∈ uIcc c₁ c₂, f c = ave := by
    apply intermediate_value_uIcc
    · refine ContinuousOn.mono hf ?_
      rwa [uIcc_of_le h]
    · rw [mem_uIcc]
      grind
  rcases h_ivt with ⟨c, hc_mem, hfc⟩
  refine ⟨c, ?_, hfc⟩
  rw [mem_uIcc] at hc_mem
  apply mem_uIoo_of_lt
  · grind
  · grind

/-- The mean value theorem for integrals:
There exists a point in an interval such that the mean of a continuous function over the interval
equals the value of the function at the point. -/
theorem exists_eq_interval_average
    {f : ℝ → ℝ} {a b : ℝ} (hab : a ≠ b) (hf : ContinuousOn f (uIcc a b)) :
    ∃ c ∈ uIoo a b, f c = ⨍ (x : ℝ) in a..b, f x := by
  wlog hle : a ≤ b generalizing a b
  · rw [uIoo_comm, uIoc_comm]
    apply this hab.symm ?_ (by grind)
    rwa [uIcc_comm]
  have : Ι a b = Ioc a b := uIoc_of_le hle
  apply exists_eq_interval_average_of_NoAtoms hf
  · simp [this]
  · apply ne_of_gt
    rw [this, Real.volume_Ioc, ENNReal.ofReal_pos]
    grind
