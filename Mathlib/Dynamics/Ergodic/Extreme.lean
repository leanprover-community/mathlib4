/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Decomposition.RadonNikodym

/-!
TODO
-/

open Filter Set Function MeasureTheory Measure ProbabilityTheory
open scoped NNReal ENNReal

variable {α : Type*} {m : MeasurableSpace α} {μ ν : Measure α} {f : α → α}

namespace Ergodic

/-- Given a constant `c ≠ ∞`, an extreme point of the set of measures that are invariant under `f`
and have total mass `c` is an ergodic measure. -/
theorem of_mem_extremePoints_meas_univ {c : ℝ≥0∞} (hc : c ≠ ∞)
    (h : μ ∈ extremePoints ℝ≥0∞ {ν | MeasurePreserving f ν ν ∧ ν univ = c}) : Ergodic f μ := by
  have hf : MeasurePreserving f μ μ := h.1.1
  rcases eq_or_ne c 0 with rfl | hc₀
  · convert Ergodic.zero_measure hf.measurable
    rw [← Measure.measure_univ_eq_zero, h.1.2]
  · refine ⟨hf, ⟨?_⟩⟩
    have hfin : IsFiniteMeasure μ := by
      constructor
      rwa [h.1.2, lt_top_iff_ne_top]
    set S := {ν | MeasurePreserving f ν ν ∧ ν univ = c}
    have : ∀ s, MeasurableSet s → f ⁻¹' s = s → μ s ≠ 0 → c • μ[|s] ∈ S := by
      intro s hsm hfs hμs
      refine ⟨.smul_measure (.smul_measure ?_ _) c, ?_⟩
      · -- TODO: add `MeasurePreserving.restrict` and use it here
        refine ⟨hf.measurable, ?_⟩
        ext t ht
        rw [Measure.map_apply hf.measurable ht, Measure.restrict_apply' hsm,
          Measure.restrict_apply' hsm]
        nth_rewrite 1 [← hfs]
        rw [← preimage_inter, hf.measure_preimage (ht.inter hsm).nullMeasurableSet]
      · rw [Measure.smul_apply, (cond_isProbabilityMeasure hμs).1, smul_eq_mul, mul_one]
    intro s hsm hfs
    by_contra H
    obtain ⟨hs, hs'⟩ : μ s ≠ 0 ∧ μ sᶜ ≠ 0 := by
      simpa [eventuallyConst_set, ae_iff, and_comm] using H
    obtain ⟨hcond, -⟩ : c • μ[|s] = μ ∧ c • μ[|sᶜ] = μ := by
      apply h.2 (this s hsm hfs hs) (this sᶜ hsm.compl (by rw [preimage_compl, hfs]) hs')
      refine ⟨μ s / c, μ sᶜ / c, ENNReal.div_pos hs hc, ENNReal.div_pos hs' hc, ?_, ?_⟩
      · rw [← ENNReal.add_div, measure_add_measure_compl hsm, h.1.2, ENNReal.div_self hc₀ hc]
      · simp [ProbabilityTheory.cond, smul_smul, ← mul_assoc, ENNReal.div_mul_cancel,
          ENNReal.mul_inv_cancel, *]
    rw [← hcond] at hs'
    simp [ProbabilityTheory.cond_apply, hsm] at hs'

/-- An extreme point of the set of invariant probability measures is an ergodic measure. -/
theorem of_mem_extremePoints
    (h : μ ∈ extremePoints ℝ≥0∞ {ν | MeasurePreserving f ν ν ∧ IsProbabilityMeasure ν}) :
    Ergodic f μ :=
  .of_mem_extremePoints_meas_univ ENNReal.one_ne_top <| by
    simpa only [isProbabilityMeasure_iff] using h

theorem eq_of_absolutelyContinuous [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Ergodic f μ) (hfν : MeasurePreserving f ν ν) (hνμ : ν ≪ μ) : ν = μ := by
  have hfm : Measurable f := hfν.measurable
  have H₁ : ∀ s, MeasurableSet s → ν (f ⁻¹' s \ s) = ν (s \ f ⁻¹' s) := by
    intro s hs
    apply measure_diff_symm _ _ (hfν.measure_preimage _) <;>
      first | apply measure_ne_top | measurability
  obtain ⟨ρ, hρm, rfl⟩ : ∃ ρ, Measurable ρ ∧ ν = μ.withDensity ρ :=
    ⟨ν.rnDeriv μ, ν.measurable_rnDeriv μ, .symm <| Measure.withDensity_rnDeriv_eq _ _ hνμ⟩
  have H₂ : ∀ c, f ⁻¹' (ρ ⁻¹' Iio c) =ᵐ[μ] ρ ⁻¹' Iio c := by
    intro c
    specialize H₁ (ρ ⁻¹' Iio c) (by measurability)
    rw [withDensity_apply, withDensity_apply] at H₁ <;> try measurability
  have H₃ : ∀ s, MeasurableSet s → ∫⁻ a in f ⁻¹' s, ρ a ∂μ = ∫⁻ a in s, ρ a ∂μ := by
    intro s hs
    rw [← withDensity_apply, hfν.measure_preimage hs.nullMeasurableSet, withDensity_apply]
    exacts [hs, hfν.measurable hs]

  suffices ρ =ᵐ[μ] 1 by rw [withDensity_congr_ae this, withDensity_one]
  set s := {x | ρ x < 1}


theorem eq_smul_of_absolutelyContinuous [IsFiniteMeasure μ] (hμ : Ergodic f μ)
    (hfν : MeasurePreserving f ν ν) (hνμ : ν ≪ μ) : ∃ c : ℝ≥0∞, ν = c • μ := by
  wlog hpμ : IsProbabilityMeasure μ generalizing μ
  ·
  sorry

end Ergodic
