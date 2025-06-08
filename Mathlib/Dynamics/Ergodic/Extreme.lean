/-
Copyright (c) 2025 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Dynamics.Ergodic.Function
import Mathlib.Dynamics.Ergodic.RadonNikodym
import Mathlib.Probability.ConditionalProbability

/-!
# Ergodic measures as extreme points

In this file we prove that a finite measure `μ` is an ergodic measure for a self-map `f`
iff it is an extreme point of the set of invariant measures of `f` with the same total volume.
We also specialize this result to probability measures.
-/

open Filter Set Function MeasureTheory Measure ProbabilityTheory
open scoped NNReal ENNReal Topology

variable {X : Type*} {m : MeasurableSpace X} {μ ν : Measure X} {f : X → X}

namespace Ergodic

/-- Given a constant `c ≠ ∞`, an extreme point of the set of measures that are invariant under `f`
and have total mass `c` is an ergodic measure. -/
theorem of_mem_extremePoints_measure_univ_eq {c : ℝ≥0∞} (hc : c ≠ ∞)
    (h : μ ∈ extremePoints ℝ≥0∞ {ν | MeasurePreserving f ν ν ∧ ν univ = c}) : Ergodic f μ := by
  have hf : MeasurePreserving f μ μ := h.1.1
  rcases eq_or_ne c 0 with rfl | hc₀
  · convert zero_measure hf.measurable
    rw [← measure_univ_eq_zero, h.1.2]
  · refine ⟨hf, ⟨?_⟩⟩
    have : IsFiniteMeasure μ := by
      constructor
      rwa [h.1.2, lt_top_iff_ne_top]
    set S := {ν | MeasurePreserving f ν ν ∧ ν univ = c}
    have {s : Set X} (hsm : MeasurableSet s) (hfs : f ⁻¹' s = s) (hμs : μ s ≠ 0) :
        c • μ[|s] ∈ S := by
      refine ⟨.smul_measure (.smul_measure ?_ _) c, ?_⟩
      · convert hf.restrict_preimage hsm
        exact hfs.symm
      · rw [Measure.smul_apply, (cond_isProbabilityMeasure hμs).1, smul_eq_mul, mul_one]
    intro s hsm hfs
    by_contra H
    obtain ⟨hs, hs'⟩ : μ s ≠ 0 ∧ μ sᶜ ≠ 0 := by
      simpa [eventuallyConst_set, ae_iff, and_comm] using H
    obtain ⟨hcond, -⟩ : c • μ[|s] = μ ∧ c • μ[|sᶜ] = μ := by
      apply h.2 (this hsm hfs hs) (this hsm.compl (by rw [preimage_compl, hfs]) hs')
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
  .of_mem_extremePoints_measure_univ_eq ENNReal.one_ne_top <| by
    simpa only [isProbabilityMeasure_iff] using h

-- TODO: do we need `IsFiniteMeasure ν` here?
theorem eq_smul_of_absolutelyContinuous [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμ : Ergodic f μ)
    (hfν : MeasurePreserving f ν ν) (hνμ : ν ≪ μ) : ∃ c : ℝ≥0∞, ν = c • μ := by
  have := hfν.rnDeriv_comp_aeEq hμ.toMeasurePreserving
  obtain ⟨c, hc⟩ := hμ.ae_eq_const_of_ae_eq_comp₀ (measurable_rnDeriv _ _).nullMeasurable this
  use c
  ext s hs
  calc
    ν s = ∫⁻ a in s, ν.rnDeriv μ a ∂μ := .symm <| setLIntegral_rnDeriv hνμ _
    _ = ∫⁻ _ in s, c ∂μ := lintegral_congr_ae <| hc.filter_mono <| ae_mono restrict_le_self
    _ = (c • μ) s := by simp

theorem eq_of_absolutelyContinuous_measure_univ_eq [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : Ergodic f μ) (hfν : MeasurePreserving f ν ν) (hνμ : ν ≪ μ) (huniv : ν univ = μ univ) :
    ν = μ := by
  rcases hμ.eq_smul_of_absolutelyContinuous hfν hνμ with ⟨c, rfl⟩
  rcases eq_or_ne μ 0 with rfl | hμ₀
  · simp
  · simp_all [ENNReal.mul_eq_right]

theorem eq_of_absolutelyContinuous [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Ergodic f μ) (hfν : MeasurePreserving f ν ν) (hνμ : ν ≪ μ) : ν = μ :=
  eq_of_absolutelyContinuous_measure_univ_eq hμ hfν hνμ <| by simp

theorem mem_extremePoints_measure_univ_eq [IsFiniteMeasure μ] (hμ : Ergodic f μ) :
    μ ∈ extremePoints ℝ≥0∞ {ν | MeasurePreserving f ν ν ∧ ν univ = μ univ} := by
  rw [mem_extremePoints_iff_left]
  refine ⟨⟨hμ.toMeasurePreserving, rfl⟩, ?_⟩
  rintro ν₁ ⟨hfν₁, hν₁μ⟩ ν₂ ⟨hfν₂, hν₂μ⟩ ⟨a, b, ha, hb, hab, rfl⟩
  have : IsFiniteMeasure ν₁ := ⟨by rw [hν₁μ]; apply measure_lt_top⟩
  apply hμ.eq_of_absolutelyContinuous_measure_univ_eq hfν₁ (.add_right _ _) hν₁μ
  apply absolutelyContinuous_smul ha.ne'

theorem mem_extremePoints [IsProbabilityMeasure μ] (hμ : Ergodic f μ) :
    μ ∈ extremePoints ℝ≥0∞ {ν | MeasurePreserving f ν ν ∧ IsProbabilityMeasure ν} := by
  simpa only [isProbabilityMeasure_iff, measure_univ] using hμ.mem_extremePoints_measure_univ_eq

theorem iff_mem_extremePoints_measure_univ_eq [IsFiniteMeasure μ] :
    Ergodic f μ ↔ μ ∈ extremePoints ℝ≥0∞ {ν | MeasurePreserving f ν ν ∧ ν univ = μ univ} :=
  ⟨mem_extremePoints_measure_univ_eq, of_mem_extremePoints_measure_univ_eq (measure_ne_top _ _)⟩

theorem iff_mem_extremePoints [IsProbabilityMeasure μ] :
    Ergodic f μ ↔ μ ∈ extremePoints ℝ≥0∞ {ν | MeasurePreserving f ν ν ∧ IsProbabilityMeasure ν} :=
  ⟨mem_extremePoints, of_mem_extremePoints⟩

end Ergodic
