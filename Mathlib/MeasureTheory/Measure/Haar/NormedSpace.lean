/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Sébastien Gouëzel
-/
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Integral.Bochner

#align_import measure_theory.measure.haar.normed_space from "leanprover-community/mathlib"@"b84aee748341da06a6d78491367e2c0e9f15e8a5"

/-!
# Basic properties of Haar measures on real vector spaces

-/

noncomputable section

open scoped NNReal ENNReal Pointwise BigOperators Topology

open Inv Set Function MeasureTheory.Measure Filter

open FiniteDimensional

namespace MeasureTheory

namespace Measure

/- The instance `MeasureTheory.Measure.IsAddHaarMeasure.noAtoms` applies in particular to show that
an additive Haar measure on a nontrivial finite-dimensional real vector space has no atom. -/
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [IsAddHaarMeasure μ] : NoAtoms μ := by
  infer_instance

section ContinuousLinearEquiv

variable {𝕜 G H : Type*} [MeasurableSpace G] [MeasurableSpace H] [NontriviallyNormedField 𝕜]
  [TopologicalSpace G] [TopologicalSpace H] [AddCommGroup G] [AddCommGroup H]
  [TopologicalAddGroup G] [TopologicalAddGroup H] [Module 𝕜 G] [Module 𝕜 H] (μ : Measure G)
  [IsAddHaarMeasure μ] [BorelSpace G] [BorelSpace H] [T2Space H]

instance MapContinuousLinearEquiv.isAddHaarMeasure (e : G ≃L[𝕜] H) : IsAddHaarMeasure (μ.map e) :=
  e.toAddEquiv.isAddHaarMeasure_map _ e.continuous e.symm.continuous
#align measure_theory.measure.map_continuous_linear_equiv.is_add_haar_measure MeasureTheory.Measure.MapContinuousLinearEquiv.isAddHaarMeasure

variable [CompleteSpace 𝕜] [T2Space G] [FiniteDimensional 𝕜 G] [ContinuousSMul 𝕜 G]
  [ContinuousSMul 𝕜 H]

instance MapLinearEquiv.isAddHaarMeasure (e : G ≃ₗ[𝕜] H) : IsAddHaarMeasure (μ.map e) :=
  MapContinuousLinearEquiv.isAddHaarMeasure _ e.toContinuousLinearEquiv
#align measure_theory.measure.map_linear_equiv.is_add_haar_measure MeasureTheory.Measure.MapLinearEquiv.isAddHaarMeasure

end ContinuousLinearEquiv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] (μ : Measure E) [IsAddHaarMeasure μ] {F : Type*} [NormedAddCommGroup F]
  [NormedSpace ℝ F]

variable {s : Set E}

/-- The integral of `f (R • x)` with respect to an additive Haar measure is a multiple of the
integral of `f`. The formula we give works even when `f` is not integrable or `R = 0`
thanks to the convention that a non-integrable function has integral zero. -/
theorem integral_comp_smul (f : E → F) (R : ℝ) :
    (∫ x, f (R • x) ∂μ) = |(R ^ finrank ℝ E)⁻¹| • ∫ x, f x ∂μ := by
  by_cases hF : CompleteSpace F; swap
  · simp [integral, hF]
  rcases eq_or_ne R 0 with (rfl | hR)
  · simp only [zero_smul, integral_const]
    rcases Nat.eq_zero_or_pos (finrank ℝ E) with (hE | hE)
    · have : Subsingleton E := finrank_zero_iff.1 hE
      have : f = fun _ => f 0 := by ext x; rw [Subsingleton.elim x 0]
      conv_rhs => rw [this]
      simp only [hE, pow_zero, inv_one, abs_one, one_smul, integral_const]
    · have : Nontrivial E := finrank_pos_iff.1 hE
      simp only [zero_pow hE.ne', measure_univ_of_isAddLeftInvariant, ENNReal.top_toReal, zero_smul,
        inv_zero, abs_zero]
  · calc
      (∫ x, f (R • x) ∂μ) = ∫ y, f y ∂Measure.map (fun x => R • x) μ :=
        (integral_map_equiv (Homeomorph.smul (isUnit_iff_ne_zero.2 hR).unit).toMeasurableEquiv
            f).symm
      _ = |(R ^ finrank ℝ E)⁻¹| • ∫ x, f x ∂μ := by
        simp only [map_addHaar_smul μ hR, integral_smul_measure, ENNReal.toReal_ofReal, abs_nonneg]
#align measure_theory.measure.integral_comp_smul MeasureTheory.Measure.integral_comp_smul

/-- The integral of `f (R • x)` with respect to an additive Haar measure is a multiple of the
integral of `f`. The formula we give works even when `f` is not integrable or `R = 0`
thanks to the convention that a non-integrable function has integral zero. -/
theorem integral_comp_smul_of_nonneg (f : E → F) (R : ℝ) {hR : 0 ≤ R} :
    (∫ x, f (R • x) ∂μ) = (R ^ finrank ℝ E)⁻¹ • ∫ x, f x ∂μ := by
  rw [integral_comp_smul μ f R, abs_of_nonneg (inv_nonneg.2 (pow_nonneg hR _))]
#align measure_theory.measure.integral_comp_smul_of_nonneg MeasureTheory.Measure.integral_comp_smul_of_nonneg

/-- The integral of `f (R⁻¹ • x)` with respect to an additive Haar measure is a multiple of the
integral of `f`. The formula we give works even when `f` is not integrable or `R = 0`
thanks to the convention that a non-integrable function has integral zero. -/
theorem integral_comp_inv_smul (f : E → F) (R : ℝ) :
    (∫ x, f (R⁻¹ • x) ∂μ) = |R ^ finrank ℝ E| • ∫ x, f x ∂μ := by
  rw [integral_comp_smul μ f R⁻¹, inv_pow, inv_inv]
#align measure_theory.measure.integral_comp_inv_smul MeasureTheory.Measure.integral_comp_inv_smul

/-- The integral of `f (R⁻¹ • x)` with respect to an additive Haar measure is a multiple of the
integral of `f`. The formula we give works even when `f` is not integrable or `R = 0`
thanks to the convention that a non-integrable function has integral zero. -/
theorem integral_comp_inv_smul_of_nonneg (f : E → F) {R : ℝ} (hR : 0 ≤ R) :
    (∫ x, f (R⁻¹ • x) ∂μ) = R ^ finrank ℝ E • ∫ x, f x ∂μ := by
  rw [integral_comp_inv_smul μ f R, abs_of_nonneg (pow_nonneg hR _)]
#align measure_theory.measure.integral_comp_inv_smul_of_nonneg MeasureTheory.Measure.integral_comp_inv_smul_of_nonneg

theorem integral_comp_mul_left (g : ℝ → F) (a : ℝ) : (∫ x : ℝ, g (a * x)) = |a⁻¹| • ∫ y : ℝ, g y :=
  by simp_rw [← smul_eq_mul, Measure.integral_comp_smul, FiniteDimensional.finrank_self, pow_one]
#align measure_theory.measure.integral_comp_mul_left MeasureTheory.Measure.integral_comp_mul_left

theorem integral_comp_inv_mul_left (g : ℝ → F) (a : ℝ) :
    (∫ x : ℝ, g (a⁻¹ * x)) = |a| • ∫ y : ℝ, g y := by
  simp_rw [← smul_eq_mul, Measure.integral_comp_inv_smul, FiniteDimensional.finrank_self, pow_one]
#align measure_theory.measure.integral_comp_inv_mul_left MeasureTheory.Measure.integral_comp_inv_mul_left

theorem integral_comp_mul_right (g : ℝ → F) (a : ℝ) : (∫ x : ℝ, g (x * a)) = |a⁻¹| • ∫ y : ℝ, g y :=
  by simpa only [mul_comm] using integral_comp_mul_left g a
#align measure_theory.measure.integral_comp_mul_right MeasureTheory.Measure.integral_comp_mul_right

theorem integral_comp_inv_mul_right (g : ℝ → F) (a : ℝ) :
    (∫ x : ℝ, g (x * a⁻¹)) = |a| • ∫ y : ℝ, g y := by
  simpa only [mul_comm] using integral_comp_inv_mul_left g a
#align measure_theory.measure.integral_comp_inv_mul_right MeasureTheory.Measure.integral_comp_inv_mul_right

theorem integral_comp_div (g : ℝ → F) (a : ℝ) : (∫ x : ℝ, g (x / a)) = |a| • ∫ y : ℝ, g y :=
  integral_comp_inv_mul_right g a
#align measure_theory.measure.integral_comp_div MeasureTheory.Measure.integral_comp_div

end Measure

variable {F : Type*} [NormedAddCommGroup F]

theorem integrable_comp_smul_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] (μ : Measure E) [IsAddHaarMeasure μ]
    (f : E → F) {R : ℝ} (hR : R ≠ 0) : Integrable (fun x => f (R • x)) μ ↔ Integrable f μ := by
  -- reduce to one-way implication
  suffices
    ∀ {g : E → F} (_ : Integrable g μ) {S : ℝ} (_ : S ≠ 0), Integrable (fun x => g (S • x)) μ by
    refine' ⟨fun hf => _, fun hf => this hf hR⟩
    convert this hf (inv_ne_zero hR)
    rw [← mul_smul, mul_inv_cancel hR, one_smul]
  -- now prove
  intro g hg S hS
  let t := ((Homeomorph.smul (isUnit_iff_ne_zero.2 hS).unit).toMeasurableEquiv : E ≃ᵐ E)
  refine' (integrable_map_equiv t g).mp (_ : Integrable g (map (S • ·) μ))
  rwa [map_addHaar_smul μ hS, integrable_smul_measure _ ENNReal.ofReal_ne_top]
  simpa only [Ne.def, ENNReal.ofReal_eq_zero, not_le, abs_pos] using inv_ne_zero (pow_ne_zero _ hS)
#align measure_theory.integrable_comp_smul_iff MeasureTheory.integrable_comp_smul_iff

theorem Integrable.comp_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] {μ : Measure E} [IsAddHaarMeasure μ]
    {f : E → F} (hf : Integrable f μ) {R : ℝ} (hR : R ≠ 0) : Integrable (fun x => f (R • x)) μ :=
  (integrable_comp_smul_iff μ f hR).2 hf
#align measure_theory.integrable.comp_smul MeasureTheory.Integrable.comp_smul

theorem integrable_comp_mul_left_iff (g : ℝ → F) {R : ℝ} (hR : R ≠ 0) :
    (Integrable fun x => g (R * x)) ↔ Integrable g := by
  simpa only [smul_eq_mul] using integrable_comp_smul_iff volume g hR
#align measure_theory.integrable_comp_mul_left_iff MeasureTheory.integrable_comp_mul_left_iff

theorem Integrable.comp_mul_left' {g : ℝ → F} (hg : Integrable g) {R : ℝ} (hR : R ≠ 0) :
    Integrable fun x => g (R * x) :=
  (integrable_comp_mul_left_iff g hR).2 hg
#align measure_theory.integrable.comp_mul_left' MeasureTheory.Integrable.comp_mul_left'

theorem integrable_comp_mul_right_iff (g : ℝ → F) {R : ℝ} (hR : R ≠ 0) :
    (Integrable fun x => g (x * R)) ↔ Integrable g := by
  simpa only [mul_comm] using integrable_comp_mul_left_iff g hR
#align measure_theory.integrable_comp_mul_right_iff MeasureTheory.integrable_comp_mul_right_iff

theorem Integrable.comp_mul_right' {g : ℝ → F} (hg : Integrable g) {R : ℝ} (hR : R ≠ 0) :
    Integrable fun x => g (x * R) :=
  (integrable_comp_mul_right_iff g hR).2 hg
#align measure_theory.integrable.comp_mul_right' MeasureTheory.Integrable.comp_mul_right'

theorem integrable_comp_div_iff (g : ℝ → F) {R : ℝ} (hR : R ≠ 0) :
    (Integrable fun x => g (x / R)) ↔ Integrable g :=
  integrable_comp_mul_right_iff g (inv_ne_zero hR)
#align measure_theory.integrable_comp_div_iff MeasureTheory.integrable_comp_div_iff

theorem Integrable.comp_div {g : ℝ → F} (hg : Integrable g) {R : ℝ} (hR : R ≠ 0) :
    Integrable fun x => g (x / R) :=
  (integrable_comp_div_iff g hR).2 hg
#align measure_theory.integrable.comp_div MeasureTheory.Integrable.comp_div

section InnerProductSpace

variable {E' F' A : Type*}
variable [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']
  [MeasurableSpace E'] [BorelSpace E']
variable [NormedAddCommGroup F'] [InnerProductSpace ℝ F'] [FiniteDimensional ℝ F']
  [MeasurableSpace F'] [BorelSpace F']

variable (f : E' ≃ₗᵢ[ℝ] F')

variable [NormedAddCommGroup A] [NormedSpace ℝ A]

theorem integrable_comp (g : F' → A) : Integrable (g ∘ f) ↔ Integrable g :=
  f.measurePreserving.integrable_comp_emb f.toMeasureEquiv.measurableEmbedding

theorem integral_comp (g : F' → A) : ∫ (x : E'), g (f x) = ∫ (y : F'), g y :=
  f.measurePreserving.integral_comp' (f := f.toMeasureEquiv) g

end InnerProductSpace

end MeasureTheory
