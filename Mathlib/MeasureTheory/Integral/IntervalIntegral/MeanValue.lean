/-
Copyright (c) 2025 Louis (Yiyang) Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Louis (Yiyang) Liu
-/
import Mathlib.MeasureTheory.Integral.IntervalAverage

/-!
# First mean value theorem for integrals

We prove versions of the first mean value theorem for (unordered) interval integrals
w.r.t. an arbitrary measure in `ℝ`

One assuming almost-everywhere nonnegativity of `g` under an arbitrary measure,
and one assuming pointwise nonnegativity together with continuity of `g`.

## Main statements

- `exists_eq_const_mul_integral_of_ae_nonneg`:
    **First mean value theorem for integrals** for (unordered) interval integrals when
    `g` is interval integrable on `a..b` w.r.t. an arbitrary measure `μ` and satisfies
    `g ≥ 0` almost everywhere on `uIoc a b`.
- `exists_eq_const_mul_integral_of_nonneg`:
    **First mean value theorem for integrals** for (unordered) interval integrals when
    `g` is continuous on `uIoc a b` and nonnegative there (Lebesgue measure).

## References

* [V. A. Zorich, *Mathematical Analysis I*][zorich2016],
    Thm. 5 (First mean-value theorem for the integral).
* <https://proofwiki.org/wiki/Mean_Value_Theorem_for_Integrals/Generalization>

## Tags

mean value theorem, interval integral, measure, nonnegative, continuous, integrable
-/

open MeasureTheory Set intervalIntegral

/-- **First mean value theorem for integrals (interval integral, arbitrary measure).**
Let `μ` be a measure on `ℝ`. If `f : ℝ → ℝ` is continuous on `uIcc a b` and
`g : ℝ → ℝ` is interval integrable on `a..b` w.r.t. `μ`, and `g ≥ 0` almost
everywhere on `uIoc a b`, then there exists `c ∈ uIcc a b` such that
`∫ x in a..b, f x * g x ∂μ = f c * ∫ x in a..b, g x ∂μ`. -/
theorem exists_eq_const_mul_integral_of_ae_nonneg
    {a b : ℝ} {f g : ℝ → ℝ} {μ : Measure ℝ}
    (hf : ContinuousOn f (uIcc a b))
    (hg : IntervalIntegrable g μ a b)
    (hg0 : ∀ᵐ x ∂(μ.restrict (uIoc a b)), 0 ≤ g x) :
    ∃ c ∈ uIcc a b, (∫ x in a..b, f x * g x ∂μ) = f c * (∫ x in a..b, g x ∂μ) := by
  wlog hle : a ≤ b generalizing a b
  · simp at hle
    obtain ⟨c, c_in_uIcc, that⟩ :=
      this (a := b) (b := a) (by rwa [uIcc_comm]) hg.symm (by rwa [uIoc_comm]) hle.le
    refine ⟨c, by rwa [uIcc_comm], by simpa [integral_symm b a]⟩
  let s := uIoc a b
  have hs : s = Ioc a b := uIoc_of_le hle
  have hs_meas : MeasurableSet s := measurableSet_uIoc
  let ρ := fun x ↦ ENNReal.ofReal (g x)
  let ν := μ.withDensity ρ
  have hρ_ae : AEMeasurable ρ (μ.restrict s) := by
    apply AEMeasurable.ennreal_ofReal
    apply AEStronglyMeasurable.aemeasurable
    apply IntervalIntegrable.aestronglyMeasurable
    simpa [hle]
  have hρ_top : ∀ᵐ x ∂ μ.restrict s, ρ x < ⊤ := by simp [ρ]
  have h_toReal_ae : (fun x ↦ (ρ x).toReal) =ᵐ[μ.restrict s] g := by
    apply hg0.mono
    intro x hx
    simpa [ρ]
  have hfg : ∫ x in a..b, f x * g x ∂μ = ∫ x in s, f x ∂ν := by
    calc
      _ = ∫ x in s, f x * g x ∂μ := by simp [hs, integral_of_le hle]
      _ = ∫ x in s, (ρ x).toReal * f x ∂μ := by
        apply MeasureTheory.integral_congr_ae
        apply h_toReal_ae.mono
        intro x hx
        simp [hx, mul_comm]
      _ = _ := by
        have h := setIntegral_withDensity_eq_setIntegral_toReal_smul₀
          hρ_ae hρ_top f hs_meas
        simp [ν, h]
  have hg1 : ∫ x in a..b, g x ∂μ = ∫ x in s, (1 : ℝ) ∂ν := by
    have h := setIntegral_withDensity_eq_setIntegral_toReal_smul₀
      hρ_ae hρ_top (fun _ ↦ (1 : ℝ)) hs_meas
    calc
      _ = ∫ x in s, g x ∂μ := by simp [hs, integral_of_le hle]
      _ = ∫ x in s, (ρ x).toReal ∂μ := by rw [integral_congr_ae h_toReal_ae]
      _ = _ := by simp [ν, h]
  by_cases hzero : ∫ x in s, (1 : ℝ) ∂ν = 0
  · refine ⟨a, by simp, ?_⟩
    calc
      _ = ∫ x in s, f x ∂ν := hfg
      _ = 0 := by
        rw [hzero, integral_eq_zero_iff_of_le_of_nonneg_ae
          hle (by rwa [← uIoc_of_le hle]) hg, ← uIoc_of_le hle] at hg1
        have hfg_zero : ∫ x in a..b, f x * g x ∂μ = 0 := by
          have hfg_ae : (fun x ↦ f x * g x) =ᵐ[μ.restrict s] 0 := by
            apply hg1.mono
            intro x hx
            simp [hx]
          simp [integral_congr_ae_restrict hfg_ae]
        rw [← hfg, hfg_zero]
      _ = _ := by simp [hzero, hg1]
  · have hzero' : (ν s).toReal ≠ 0 := by simpa using hzero
    have hνfin : ν s ≠ ⊤ := by
      intro this
      apply hzero'
      simp [this]
    have hν0 : ν s ≠ 0 := by
      intro this
      apply hzero'
      simp [this]
    obtain ⟨c, hc, havg⟩ := exists_eq_interval_average_of_measure
      hf hνfin hν0
    refine ⟨c, hc, ?_⟩
    calc
      _ = ∫ x in s, f x ∂ν := hfg
      _ = f c * ∫ x in s, (1 : ℝ) ∂ν := by
        rw [havg]
        refold_let s
        simp [setAverage_eq]
        rw [measureReal_def]
        have hreal0 : (ν s).toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hν0, hνfin⟩
        field_simp
      _ = _ := by simp [hg1]

/-- **First mean value theorem for integrals (interval integral).**
Let `f g : ℝ → ℝ` be continuous on `uIcc a b`. If `g ≥ 0` on `uIoc a b`,
then there exists `c ∈ uIcc a b` such that
`∫ x in a..b, f x * g x = f c * ∫ x in a..b, g x`. -/
theorem exists_eq_const_mul_integral_of_nonneg
    {a b : ℝ} {f g : ℝ → ℝ}
    (hf : ContinuousOn f (uIcc a b))
    (hg : ContinuousOn g (uIcc a b))
    (hg0 : ∀ x ∈ uIoc a b, 0 ≤ g x) :
    ∃ c ∈ uIcc a b, (∫ x in a..b, f x * g x) = f c * (∫ x in a..b, g x) := by
  have hg0_ae : ∀ᵐ x ∂(volume.restrict (uIoc a b)), 0 ≤ g x := by
    rw [ae_restrict_iff' measurableSet_uIoc]
    exact ae_of_all volume hg0
  exact exists_eq_const_mul_integral_of_ae_nonneg
    hf hg.intervalIntegrable hg0_ae
