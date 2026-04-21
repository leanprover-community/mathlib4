/-
Copyright (c) 2025 Louis (Yiyang) Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Louis (Yiyang) Liu
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.MeanValue

/-!
# First mean value theorem for interval integrals

We prove versions of the first mean value theorem for interval integrals.

## Main results

* `exists_eq_const_mul_intervalIntegral_of_ae_nonneg` (a.e. nonnegativity of `g` on `s`):
    `∃ c ∈ uIcc a b, (∫ x in a..b, f x * g x ∂μ) = f c * (∫ x in a..b, g x ∂μ)`.
* `exists_eq_const_mul_intervalIntegral_of_nonneg` (pointwise nonnegativity of `g` on `s`):
    `∃ c ∈ uIcc a b, (∫ x in a..b, f x * g x ∂μ) = f c * (∫ x in a..b, g x ∂μ)`.

## References

* [V. A. Zorich, *Mathematical Analysis I*][zorich2016],
    Thm. 5 (First mean-value theorem for the integral).
* <https://proofwiki.org/wiki/Mean_Value_Theorem_for_Integrals/Generalization>

## Tags

mean value theorem, interval integral
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

open MeasureTheory Set intervalIntegral

open scoped Interval

variable {a b : ℝ} {f g : ℝ → ℝ} {μ : Measure ℝ}

/-- **First mean value theorem for interval integrals (arbitrary measure, a.e. nonnegativity).**
Let `f g : ℝ → ℝ` and let `μ` be a measure on `ℝ`. Assume that `f` is continuous on `uIcc a b`,
that `g` is interval integrable on `a..b` w.r.t. `μ`, and that `g ≥ 0` a.e. on `Ι a b` w.r.t.
`μ.restrict (Ι a b)`. Then
`∃ c ∈ uIcc a b, (∫ x in a..b, f x * g x ∂μ) = f c * (∫ x in a..b, g x ∂μ)`. -/
theorem exists_eq_const_mul_intervalIntegral_of_ae_nonneg
    (hf : ContinuousOn f (uIcc a b)) (hg : IntervalIntegrable g μ a b)
    (hg0 : ∀ᵐ x ∂(μ.restrict (Ι a b)), 0 ≤ g x) :
    ∃ c ∈ uIcc a b, (∫ x in a..b, f x * g x ∂μ) = f c * (∫ x in a..b, g x ∂μ) := by
  by_cases h : a = b
  · subst h
    exact ⟨a, by simp, by simp⟩
  wlog hab : a < b generalizing a b
  · simp only [not_lt] at hab
    obtain ⟨c, c_in_uIcc, that⟩ :=
      this (by rwa [uIcc_comm]) hg.symm (by rwa [uIoc_comm]) (by lia) (lt_of_le_of_ne' hab h)
    exact ⟨c, by rwa [uIcc_comm], by simpa [integral_symm b a]⟩
  let s := Ι a b
  have hs : s = Ioc a b := uIoc_of_le hab.le
  have hs' : s ⊆ [[a, b]] := uIoc_subset_uIcc
  have hs_conn : IsConnected s := by simpa [hs] using isConnected_Ioc hab
  have hfg : IntegrableOn (fun x ↦ f x * g x) s μ := by
    rw [← intervalIntegrable_iff]
    exact hg.continuousOn_smul hf
  obtain ⟨c, hc, h⟩ := exists_eq_const_mul_setIntegral_of_ae_nonneg
    hs_conn measurableSet_uIoc (hf.mono hs') (by rwa [← intervalIntegrable_iff]) hfg hg0
  have h' : ∫ (x : ℝ) in a..b, f x * g x ∂μ = f c * ∫ (x : ℝ) in a..b, g x ∂μ := by
    simpa [intervalIntegral.integral_of_le hab.le, hs] using h
  exact ⟨c, mem_of_subset_of_mem hs' hc, h'⟩

/-- **First mean value theorem for interval integrals (arbitrary measure, nonnegativity).**
Let `f g : ℝ → ℝ` and let `μ` be a measure on `ℝ`. Assume that `f` is continuous on `uIcc a b`,
that `g` is interval integrable on `a..b` w.r.t. `μ`, and that `g ≥ 0` on `Ι a b`. Then
`∃ c ∈ uIcc a b, (∫ x in a..b, f x * g x ∂μ) = f c * (∫ x in a..b, g x ∂μ)`. -/
theorem exists_eq_const_mul_intervalIntegral_of_nonneg
    (hf : ContinuousOn f (uIcc a b)) (hg : IntervalIntegrable g μ a b)
    (hg0 : ∀ x ∈ Ι a b, 0 ≤ g x) :
    ∃ c ∈ uIcc a b, (∫ x in a..b, f x * g x ∂μ) = f c * (∫ x in a..b, g x ∂μ) := by
  have hg0_ae : ∀ᵐ x ∂(μ.restrict (Ι a b)), 0 ≤ g x := by
    rw [ae_restrict_iff' measurableSet_uIoc]
    exact ae_of_all μ hg0
  exact exists_eq_const_mul_intervalIntegral_of_ae_nonneg hf hg hg0_ae
