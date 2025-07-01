/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.Moments.MGFAnalytic

/-!
# Results relating `Measure.tilted` to `mgf` and `cgf`

For a random variable `X : Ω → ℝ` and a measure `μ`, the tilted measure `μ.tilted (t * X ·)` is
linked to the moment generating function (`mgf`) and the cumulant generating function (`cgf`)
of `X`.

## Main statements

* `integral_tilted_mul_self`: the integral of `X` against the tilted measure `μ.tilted (t * X ·)`
  is the first derivative of the cumulant generating function of `X` at `t`.
  `(μ.tilted (t * X ·))[X] = deriv (cgf X μ) t`
* `variance_tilted_mul`: the variance of `X` under the tilted measure `μ.tilted (t * X ·)`
  is the second derivative of the cumulant generating function of `X` at `t`.
  `Var[X; μ.tilted (t * X ·)] = iteratedDeriv 2 (cgf X μ) t`

-/


open MeasureTheory Real Set Finset

open scoped NNReal ENNReal ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ ν : Measure Ω} {X : Ω → ℝ} {t u : ℝ}

namespace ProbabilityTheory

section Apply

/-! ### Apply lemmas for `tilted` expressed with `mgf` or `cgf`. -/

lemma tilted_mul_apply_mgf' {s : Set Ω} (hs : MeasurableSet s) :
    μ.tilted (t * X ·) s = ∫⁻ a in s, ENNReal.ofReal (exp (t * X a) / mgf X μ t) ∂μ := by
  rw [tilted_apply' _ _ hs, mgf]

lemma tilted_mul_apply_mgf [SFinite μ] (s : Set Ω) :
    μ.tilted (t * X ·) s = ∫⁻ a in s, ENNReal.ofReal (exp (t * X a) / mgf X μ t) ∂μ := by
  rw [tilted_apply, mgf]

lemma tilted_mul_apply_cgf' {s : Set Ω} (hs : MeasurableSet s)
    (ht : Integrable (fun ω ↦ exp (t * X ω)) μ) :
    μ.tilted (t * X ·) s = ∫⁻ a in s, ENNReal.ofReal (exp (t * X a - cgf X μ t)) ∂μ := by
  rcases eq_zero_or_neZero μ with rfl | hμ
  · simp
  · simp_rw [tilted_mul_apply_mgf' hs, exp_sub, exp_cgf ht]

lemma tilted_mul_apply_cgf [SFinite μ] (s : Set Ω) (ht : Integrable (fun ω ↦ exp (t * X ω)) μ) :
    μ.tilted (t * X ·) s = ∫⁻ a in s, ENNReal.ofReal (exp (t * X a - cgf X μ t)) ∂μ := by
  rcases eq_zero_or_neZero μ with rfl | hμ
  · simp
  · simp_rw [tilted_mul_apply_mgf s, exp_sub, exp_cgf ht]

lemma tilted_mul_apply_eq_ofReal_integral_mgf' {s : Set Ω} (hs : MeasurableSet s) :
    μ.tilted (t * X ·) s = ENNReal.ofReal (∫ a in s, exp (t * X a) / mgf X μ t ∂μ) := by
  rw [tilted_apply_eq_ofReal_integral' _ hs, mgf]

lemma tilted_mul_apply_eq_ofReal_integral_mgf [SFinite μ] (s : Set Ω) :
    μ.tilted (t * X ·) s = ENNReal.ofReal (∫ a in s, exp (t * X a) / mgf X μ t ∂μ) := by
  rw [tilted_apply_eq_ofReal_integral _ s, mgf]

lemma tilted_mul_apply_eq_ofReal_integral_cgf' {s : Set Ω} (hs : MeasurableSet s)
    (ht : Integrable (fun ω ↦ exp (t * X ω)) μ) :
    μ.tilted (t * X ·) s = ENNReal.ofReal (∫ a in s, exp (t * X a - cgf X μ t) ∂μ) := by
  rcases eq_zero_or_neZero μ with rfl | hμ
  · simp
  · simp_rw [tilted_mul_apply_eq_ofReal_integral_mgf' hs, exp_sub]
    rwa [exp_cgf]

lemma tilted_mul_apply_eq_ofReal_integral_cgf [SFinite μ] (s : Set Ω)
    (ht : Integrable (fun ω ↦ exp (t * X ω)) μ) :
    μ.tilted (t * X ·) s = ENNReal.ofReal (∫ a in s, exp (t * X a - cgf X μ t) ∂μ) := by
  rcases eq_zero_or_neZero μ with rfl | hμ
  · simp
  · simp_rw [tilted_mul_apply_eq_ofReal_integral_mgf s, exp_sub]
    rwa [exp_cgf]

end Apply

section Integral

/-! ### Integral of `tilted` expressed with `mgf` or `cgf`. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma setIntegral_tilted_mul_eq_mgf' (g : Ω → E) {s : Set Ω} (hs : MeasurableSet s) :
    ∫ x in s, g x ∂(μ.tilted (t * X ·)) = ∫ x in s, (exp (t * X x) / mgf X μ t) • (g x) ∂μ := by
  rw [setIntegral_tilted' _ _ hs, mgf]

lemma setIntegral_tilted_mul_eq_mgf [SFinite μ] (g : Ω → E) (s : Set Ω) :
    ∫ x in s, g x ∂(μ.tilted (t * X ·)) = ∫ x in s, (exp (t * X x) / mgf X μ t) • (g x) ∂μ := by
  rw [setIntegral_tilted, mgf]

lemma setIntegral_tilted_mul_eq_cgf' (g : Ω → E) {s : Set Ω}
    (hs : MeasurableSet s) (ht : Integrable (fun ω ↦ exp (t * X ω)) μ) :
    ∫ x in s, g x ∂(μ.tilted (t * X ·)) = ∫ x in s, exp (t * X x - cgf X μ t) • (g x) ∂μ := by
  rcases eq_zero_or_neZero μ with rfl | hμ
  · simp
  · simp_rw [setIntegral_tilted_mul_eq_mgf' _ hs, exp_sub, exp_cgf ht]

lemma setIntegral_tilted_mul_eq_cgf [SFinite μ] (g : Ω → E) (s : Set Ω)
    (ht : Integrable (fun ω ↦ exp (t * X ω)) μ) :
    ∫ x in s, g x ∂(μ.tilted (t * X ·)) = ∫ x in s, exp (t * X x - cgf X μ t) • (g x) ∂μ := by
  rcases eq_zero_or_neZero μ with rfl | hμ
  · simp
  · simp_rw [setIntegral_tilted_mul_eq_mgf, exp_sub, exp_cgf ht]

lemma integral_tilted_mul_eq_mgf (g : Ω → E) :
    ∫ ω, g ω ∂(μ.tilted (t * X ·)) = ∫ ω, (exp (t * X ω) / mgf X μ t) • (g ω) ∂μ := by
  rw [integral_tilted, mgf]

lemma integral_tilted_mul_eq_cgf (g : Ω → E) (ht : Integrable (fun ω ↦ exp (t * X ω)) μ) :
    ∫ ω, g ω ∂(μ.tilted (t * X ·)) = ∫ ω, exp (t * X ω - cgf X μ t) • (g ω) ∂μ := by
  rcases eq_zero_or_neZero μ with rfl | hμ
  · simp
  · simp_rw [integral_tilted_mul_eq_mgf, exp_sub]
    rwa [exp_cgf]

/-- The integral of `X` against the tilted measure `μ.tilted (t * X ·)` is the first derivative of
the cumulant generating function of `X` at `t`. -/
lemma integral_tilted_mul_self (ht : t ∈ interior (integrableExpSet X μ)) :
    (μ.tilted (t * X ·))[X] = deriv (cgf X μ) t := by
  simp_rw [integral_tilted_mul_eq_mgf, deriv_cgf ht, ← integral_div, smul_eq_mul]
  congr with ω
  ring

end Integral

lemma memLp_tilted_mul (ht : t ∈ interior (integrableExpSet X μ)) (p : ℝ≥0) :
    MemLp X p (μ.tilted (t * X ·)) := by
  have hX : AEMeasurable X μ := aemeasurable_of_mem_interior_integrableExpSet ht
  by_cases hp : p = 0
  · simpa [hp] using hX.aestronglyMeasurable.mono_ac (tilted_absolutelyContinuous _ _)
  refine ⟨hX.aestronglyMeasurable.mono_ac (tilted_absolutelyContinuous _ _), ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top]
  rotate_left
  · simp [hp]
  · simp
  simp_rw [ENNReal.coe_toReal, ← ofReal_norm_eq_enorm, norm_eq_abs,
    ENNReal.ofReal_rpow_of_nonneg (x := |X _|) (p := p) (abs_nonneg (X _)) p.2]
  refine Integrable.lintegral_lt_top ?_
  simp_rw [integrable_tilted_iff (interior_subset (s := integrableExpSet X μ) ht),
    smul_eq_mul, mul_comm]
  exact integrable_rpow_abs_mul_exp_of_mem_interior_integrableExpSet ht p.2

/-- The variance of `X` under the tilted measure `μ.tilted (t * X ·)` is the second derivative of
the cumulant generating function of `X` at `t`. -/
lemma variance_tilted_mul (ht : t ∈ interior (integrableExpSet X μ)) :
    Var[X; μ.tilted (t * X ·)] = iteratedDeriv 2 (cgf X μ) t := by
  rw [variance_eq_integral]
  swap; · exact (memLp_tilted_mul ht 1).aestronglyMeasurable.aemeasurable
  rw [integral_tilted_mul_self ht, iteratedDeriv_two_cgf_eq_integral ht, integral_tilted_mul_eq_mgf,
    ← integral_div]
  simp only [Pi.pow_apply, Pi.sub_apply, smul_eq_mul]
  congr with ω
  ring

end ProbabilityTheory
