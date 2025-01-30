/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Moments.MGFAnalytic

/-!
# Measure tilted by a real number

This is a particular case of `Measure.tilted` where the tilting is done by a real number.

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

## Notation



## Implementation details



## References

* [F. Bar, *Quuxes*][bibkey]

## Tags

Foobars, barfoos
-/

open MeasureTheory Real Set Finset

open scoped NNReal ENNReal ProbabilityTheory

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ ν : Measure Ω} {X : Ω → ℝ} {t u : ℝ}

/-- Exponentially tilted measure. When `x ↦ exp (t * x)` is integrable, `μ.tiltedReal t` is the
probability measure with density with respect to `μ` proportional to `exp (t * x)`.
Otherwise it is 0.
-/
noncomputable
def _root_.MeasureTheory.Measure.tiltedReal (X : Ω → ℝ) (μ : Measure Ω) (t : ℝ) : Measure Ω :=
  μ.tilted (fun ω ↦ t * X ω)

instance : IsZeroOrProbabilityMeasure (μ.tiltedReal X t) := by
  rw [Measure.tiltedReal]; infer_instance

@[simp]
lemma tiltedReal_zero_measure : (0 : Measure Ω).tiltedReal X t = 0 := by simp [Measure.tiltedReal]

@[simp]
lemma tiltedReal_zero' : μ.tiltedReal X (0 : ℝ) = (μ univ)⁻¹ • μ := by simp [Measure.tiltedReal]

@[simp]
lemma todo_simp_lemma [IsZeroOrProbabilityMeasure μ] : (μ univ)⁻¹ • μ = μ := by
  rcases eq_zero_or_isProbabilityMeasure μ with h | h <;> simp [h]

lemma tiltedReal_zero [IsZeroOrProbabilityMeasure μ] : μ.tiltedReal X (0 : ℝ) = μ := by simp

lemma tiltedReal_apply' {s : Set Ω} (hs : MeasurableSet s) :
    μ.tiltedReal X t s = ∫⁻ a in s, ENNReal.ofReal (exp (t * X a) / mgf X μ t) ∂μ := by
  rw [Measure.tiltedReal, tilted_apply' _ _ hs]
  rfl

lemma tiltedReal_apply [SFinite μ] (s : Set Ω) :
    μ.tiltedReal X t s = ∫⁻ a in s, ENNReal.ofReal (exp (t * X a) / mgf X μ t) ∂μ := by
  rw [Measure.tiltedReal, tilted_apply _ _]
  rfl

lemma tiltedReal_apply_cgf [IsProbabilityMeasure μ] (s : Set Ω)
    (ht : Integrable (fun ω ↦ exp (t * X ω)) μ) :
    μ.tiltedReal X t s = ∫⁻ a in s, ENNReal.ofReal (exp (t * X a - cgf X μ t)) ∂μ := by
  simp_rw [tiltedReal_apply s, exp_sub, exp_cgf ht]

lemma tiltedReal_apply_eq_ofReal_integral' {s : Set Ω} (hs : MeasurableSet s) :
    μ.tiltedReal X t s = ENNReal.ofReal (∫ a in s, exp (t * X a) / mgf X μ t ∂μ) := by
  rw [Measure.tiltedReal, tilted_apply_eq_ofReal_integral' _ hs]
  rfl

lemma tiltedReal_apply_eq_ofReal_integral [SFinite μ] (s : Set Ω) :
    μ.tiltedReal X t s = ENNReal.ofReal (∫ a in s, exp (t * X a) / mgf X μ t ∂μ) := by
  rw [Measure.tiltedReal, tilted_apply_eq_ofReal_integral _ s]
  rfl

lemma tiltedReal_apply_eq_ofReal_integral_cgf [IsProbabilityMeasure μ] (s : Set Ω)
    (ht : Integrable (fun ω ↦ exp (t * X ω)) μ) :
    μ.tiltedReal X t s = ENNReal.ofReal (∫ a in s, exp (t * X a - cgf X μ t) ∂μ) := by
  simp_rw [tiltedReal_apply_eq_ofReal_integral s, exp_sub]
  rw [exp_cgf]
  exact ht

lemma isProbabilityMeasure_tiltedReal [NeZero μ] (hf : Integrable (fun ω ↦ exp (t * X ω)) μ) :
    IsProbabilityMeasure (μ.tiltedReal X t) :=
  isProbabilityMeasure_tilted hf

instance isZeroOrProbabilityMeasure_tiltedReal : IsZeroOrProbabilityMeasure (μ.tiltedReal X t) :=
  isZeroOrProbabilityMeasure_tilted

section Integral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- For a version that does not assume that the set is measurable, but works only for s-finite
measures, see `setIntegral_tiltedReal`. -/
lemma setIntegral_tiltedReal' (g : Ω → E) {s : Set Ω} (hs : MeasurableSet s) :
    ∫ x in s, g x ∂(μ.tiltedReal X t) = ∫ x in s, (exp (t * X x) / mgf X μ t) • (g x) ∂μ := by
  rw [Measure.tiltedReal, setIntegral_tilted' _ _ hs, mgf]

lemma setIntegral_tiltedReal [SFinite μ] (g : Ω → E) (s : Set Ω) :
    ∫ x in s, g x ∂(μ.tiltedReal X t) = ∫ x in s, (exp (t * X x) / mgf X μ t) • (g x) ∂μ := by
  rw [Measure.tiltedReal, setIntegral_tilted, mgf]

lemma integral_tiltedReal (g : Ω → E) :
    ∫ ω, g ω ∂(μ.tiltedReal X t) = ∫ ω, (exp (t * X ω) / mgf X μ t) • (g ω) ∂μ := by
  rw [Measure.tiltedReal, integral_tilted, mgf]

lemma integral_tiltedReal_self (ht : t ∈ interior (integrableExpSet X μ)) :
    (μ.tiltedReal X t)[X] = deriv (cgf X μ) t := by
  rw [integral_tiltedReal, deriv_cgf ht, ← integral_div, mgf]
  congr with ω
  rw [smul_eq_mul]
  ring

lemma tiltedReal_absolutelyContinuous (μ : Measure Ω) (X : Ω → ℝ) (t : ℝ) : μ.tiltedReal X t ≪ μ :=
  withDensity_absolutelyContinuous _ _

lemma integrable_tiltedReal_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : Ω → E) :
    Integrable g (μ.tiltedReal X t) ↔ Integrable (fun ω ↦ exp (t * X ω) • g ω) μ := by
  rw [Measure.tiltedReal, integrable_tilted_iff]

lemma memℒp_tiltedReal (ht : t ∈ interior (integrableExpSet X μ)) (p : ℝ≥0) :
    Memℒp X p (μ.tiltedReal X t) := by
  have hX : AEMeasurable X μ := aemeasurable_of_mem_interior_integrableExpSet ht
  by_cases hp : p = 0
  · simp only [hp, ENNReal.coe_zero, memℒp_zero_iff_aestronglyMeasurable]
    exact hX.aestronglyMeasurable.mono_ac (tiltedReal_absolutelyContinuous _ _ _)
  refine ⟨hX.aestronglyMeasurable.mono_ac (tiltedReal_absolutelyContinuous _ _ _), ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_nnnorm_lt_top]
  rotate_left
  · simp [hp]
  · simp
  simp_rw [ENNReal.coe_toReal, ← ofReal_norm_eq_enorm, norm_eq_abs,
    ENNReal.ofReal_rpow_of_nonneg (x := |X _|) (p := p) (abs_nonneg (X _)) p.2]
  refine Integrable.lintegral_lt_top ?_
  simp_rw [integrable_tiltedReal_iff, smul_eq_mul, mul_comm]
  exact integrable_rpow_abs_mul_exp_of_mem_interior_integrableExpSet ht p.2

lemma variance_tiltedReal (ht : t ∈ interior (integrableExpSet X μ)) :
    variance X (μ.tiltedReal X t) = iteratedDeriv 2 (cgf X μ) t := by
  rw [Memℒp.variance_eq]
  swap; · exact memℒp_tiltedReal ht 2
  rw [integral_tiltedReal_self ht, iteratedDeriv_two_cgf_eq_integral ht, integral_tiltedReal,
    ← integral_div]
  simp only [Pi.pow_apply, Pi.sub_apply, smul_eq_mul]
  congr with ω
  ring

end Integral

lemma measure_eq_integral_exp_tiltedReal [IsFiniteMeasure μ] (ε : ℝ) (t : ℝ)
    (h_int : Integrable (fun ω ↦ exp (t * X ω)) μ)
    {s : Set Ω} (hs : MeasurableSet s) :
    (μ s).toReal
      = exp (-t * ε) * mgf X μ t
      * ∫ ω, s.indicator 1 ω * exp (- t * (X ω - ε)) ∂(μ.tiltedReal X t) := by
  by_cases hμ : μ = 0
  · simp [hμ]
  calc (μ s).toReal = ∫ ω, s.indicator 1 ω ∂μ := by rw [integral_indicator_one hs]
  _ = ∫ ω, s.indicator 1 ω * exp (- t * ε - t * (X ω - ε) + t * X ω)
          * mgf X μ t / mgf X μ t ∂μ := by
    congr with ω
    have : -t * ε - t * (X ω - ε) + t * X ω = 0 := by ring
    rw [mul_div_assoc, div_self (mgf_pos' hμ h_int).ne', mul_one, this, exp_zero, mul_one]
  _ = exp (-t * ε) * mgf X μ t * ∫ ω, s.indicator 1 ω * exp (- t * (X ω - ε))
        * exp (t * X ω) / mgf X μ t ∂μ := by
      rw [← integral_mul_left]
      congr with ω
      rw [exp_add, sub_eq_add_neg, exp_add, ← neg_mul]
      ring
  _ = exp (-t * ε) * mgf X μ t
      * ∫ ω, s.indicator 1 ω * exp (- t * (X ω - ε)) ∂(μ.tiltedReal X t) := by
    rw [integral_tiltedReal]
    congr with ω
    rw [smul_eq_mul]
    ring

lemma measure_ge_eq_integral_exp_tiltedReal [IsFiniteMeasure μ] (ε : ℝ) (t : ℝ) (hX : Measurable X)
    (h_int : Integrable (fun ω ↦ exp (t * X ω)) μ) :
    (μ {ω | ε ≤ X ω}).toReal
      = exp (-t * ε) * mgf X μ t
      * ∫ ω, {ω | ε ≤ X ω}.indicator 1 ω * exp (- t * (X ω - ε)) ∂(μ.tiltedReal X t) :=
  measure_eq_integral_exp_tiltedReal _ _ h_int (hX measurableSet_Ici)

end ProbabilityTheory
