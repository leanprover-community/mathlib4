/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Measure.TiltedReal
import Mathlib.Probability.Moments.MGFAnalytic

/-!
# Results relating `Measure.tiltedReal` to `mgf` and `cgf`

## Main statements

* `fooBar_unique`

-/


open MeasureTheory Real Set Finset

open scoped NNReal ENNReal ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ ν : Measure Ω} {X : Ω → ℝ} {t u : ℝ}

namespace ProbabilityTheory

section Apply

/-! ### Apply lemmas for `tiltedReal` expressed with `mgf` or `cgf`. -/

lemma tiltedReal_apply_mgf' {s : Set Ω} (hs : MeasurableSet s) :
    μ.tiltedReal X t s = ∫⁻ a in s, ENNReal.ofReal (exp (t * X a) / mgf X μ t) ∂μ := by
  rw [Measure.tiltedReal, tilted_apply' _ _ hs]
  rfl

lemma tiltedReal_apply_mgf [SFinite μ] (s : Set Ω) :
    μ.tiltedReal X t s = ∫⁻ a in s, ENNReal.ofReal (exp (t * X a) / mgf X μ t) ∂μ := by
  rw [Measure.tiltedReal, tilted_apply _ _]
  rfl

lemma tiltedReal_apply_cgf [IsProbabilityMeasure μ] (s : Set Ω)
    (ht : Integrable (fun ω ↦ exp (t * X ω)) μ) :
    μ.tiltedReal X t s = ∫⁻ a in s, ENNReal.ofReal (exp (t * X a - cgf X μ t)) ∂μ := by
  simp_rw [tiltedReal_apply_mgf s, exp_sub, exp_cgf ht]

lemma tiltedReal_apply_eq_ofReal_integral_mgf' {s : Set Ω} (hs : MeasurableSet s) :
    μ.tiltedReal X t s = ENNReal.ofReal (∫ a in s, exp (t * X a) / mgf X μ t ∂μ) := by
  rw [tiltedReal_apply_eq_ofReal_integral' hs, mgf]

lemma tiltedReal_apply_eq_ofReal_integral_mgf [SFinite μ] (s : Set Ω) :
    μ.tiltedReal X t s = ENNReal.ofReal (∫ a in s, exp (t * X a) / mgf X μ t ∂μ) := by
  rw [tiltedReal_apply_eq_ofReal_integral s, mgf]

lemma tiltedReal_apply_eq_ofReal_integral_cgf [IsProbabilityMeasure μ] (s : Set Ω)
    (ht : Integrable (fun ω ↦ exp (t * X ω)) μ) :
    μ.tiltedReal X t s = ENNReal.ofReal (∫ a in s, exp (t * X a - cgf X μ t) ∂μ) := by
  simp_rw [tiltedReal_apply_eq_ofReal_integral_mgf s, exp_sub]
  rw [exp_cgf]
  exact ht

end Apply

section Integral

/-! ### Integral of `tiltedReal` expressed with `mgf` or `cgf`. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- For a version that does not assume that the set is measurable, but works only for s-finite
measures, see `setIntegral_tiltedReal`. -/
lemma setIntegral_tiltedReal_mgf' (g : Ω → E) {s : Set Ω} (hs : MeasurableSet s) :
    ∫ x in s, g x ∂(μ.tiltedReal X t) = ∫ x in s, (exp (t * X x) / mgf X μ t) • (g x) ∂μ := by
  rw [setIntegral_tiltedReal' _ hs, mgf]

lemma setIntegral_tiltedReal_mgf [SFinite μ] (g : Ω → E) (s : Set Ω) :
    ∫ x in s, g x ∂(μ.tiltedReal X t) = ∫ x in s, (exp (t * X x) / mgf X μ t) • (g x) ∂μ := by
  rw [setIntegral_tiltedReal, mgf]

lemma setIntegral_tiltedReal_cgf [IsProbabilityMeasure μ] (g : Ω → E) (s : Set Ω)
    (ht : Integrable (fun ω ↦ exp (t * X ω)) μ) :
    ∫ x in s, g x ∂(μ.tiltedReal X t) = ∫ x in s, exp (t * X x - cgf X μ t) • (g x) ∂μ := by
  simp_rw [setIntegral_tiltedReal_mgf, exp_sub]
  rw [exp_cgf]
  exact ht

lemma integral_tiltedReal_mgf (g : Ω → E) :
    ∫ ω, g ω ∂(μ.tiltedReal X t) = ∫ ω, (exp (t * X ω) / mgf X μ t) • (g ω) ∂μ := by
  rw [integral_tiltedReal, mgf]

lemma integral_tiltedReal_cgf [IsProbabilityMeasure μ] (g : Ω → E)
    (ht : Integrable (fun ω ↦ exp (t * X ω)) μ) :
    ∫ ω, g ω ∂(μ.tiltedReal X t) = ∫ ω, exp (t * X ω - cgf X μ t) • (g ω) ∂μ := by
  simp_rw [integral_tiltedReal_mgf, exp_sub]
  rw [exp_cgf]
  exact ht

lemma integral_tiltedReal_self (ht : t ∈ interior (integrableExpSet X μ)) :
    (μ.tiltedReal X t)[X] = deriv (cgf X μ) t := by
  simp_rw [integral_tiltedReal_mgf, deriv_cgf ht, ← integral_div, smul_eq_mul]
  congr with ω
  ring

end Integral

lemma memℒp_tiltedReal (ht : t ∈ interior (integrableExpSet X μ)) (p : ℝ≥0) :
    MemLp X p (μ.tiltedReal X t) := by
  have hX : AEMeasurable X μ := aemeasurable_of_mem_interior_integrableExpSet ht
  by_cases hp : p = 0
  · simp only [hp, ENNReal.coe_zero, memLp_zero_iff_aestronglyMeasurable]
    exact hX.aestronglyMeasurable.mono_ac (tiltedReal_absolutelyContinuous _ _ _)
  refine ⟨hX.aestronglyMeasurable.mono_ac (tiltedReal_absolutelyContinuous _ _ _), ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top]
  rotate_left
  · simp [hp]
  · simp
  simp_rw [ENNReal.coe_toReal, ← ofReal_norm_eq_enorm, norm_eq_abs,
    ENNReal.ofReal_rpow_of_nonneg (x := |X _|) (p := p) (abs_nonneg (X _)) p.2]
  refine Integrable.lintegral_lt_top ?_
  simp_rw [integrable_tiltedReal_iff (interior_subset (s := integrableExpSet X μ) ht),
    smul_eq_mul, mul_comm]
  exact integrable_rpow_abs_mul_exp_of_mem_interior_integrableExpSet ht p.2

lemma variance_tiltedReal (ht : t ∈ interior (integrableExpSet X μ)) :
    variance X (μ.tiltedReal X t) = iteratedDeriv 2 (cgf X μ) t := by
  rw [variance_eq_integral]
  swap; · exact (memℒp_tiltedReal ht 1).aestronglyMeasurable.aemeasurable
  rw [integral_tiltedReal_self ht, iteratedDeriv_two_cgf_eq_integral ht, integral_tiltedReal_mgf,
    ← integral_div]
  simp only [Pi.pow_apply, Pi.sub_apply, smul_eq_mul]
  congr with ω
  ring

end ProbabilityTheory
