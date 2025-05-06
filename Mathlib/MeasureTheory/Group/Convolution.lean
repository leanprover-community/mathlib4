/-
Copyright (c) 2023 Josha Dekker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josha Dekker
-/
import Mathlib.Analysis.LConvolution
import Mathlib.Probability.Density
import Mathlib.Probability.Independence.Basic
--import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# The multiplicative and additive convolution of measures

In this file we define and prove properties about the convolutions of two measures.

## Main definitions

* `MeasureTheory.Measure.mconv`: The multiplicative convolution of two measures: the map of `*`
  under the product measure.
* `MeasureTheory.Measure.conv`: The additive convolution of two measures: the map of `+`
  under the product measure.
-/

namespace MeasureTheory

namespace Measure
open scoped ENNReal

variable {M : Type*} [Monoid M] [MeasurableSpace M]

/-- Multiplicative convolution of measures. -/
@[to_additive "Additive convolution of measures."]
noncomputable def mconv (μ : Measure M) (ν : Measure M) :
    Measure M := Measure.map (fun x : M × M ↦ x.1 * x.2) (μ.prod ν)

/-- Scoped notation for the multiplicative convolution of measures. -/
scoped[MeasureTheory] infixr:80 " ∗ " => MeasureTheory.Measure.mconv

/-- Scoped notation for the additive convolution of measures. -/
scoped[MeasureTheory] infixr:80 " ∗ " => MeasureTheory.Measure.conv

@[to_additive]
theorem lintegral_mconv_eq_lintegral_prod [MeasurableMul₂ M] {μ ν : Measure M}
    {f : M → ℝ≥0∞} (hf : Measurable f):
    ∫⁻ z, f z ∂(μ ∗ ν) = ∫⁻ z, f (z.1 * z.2) ∂(μ.prod ν) := by
  rw[mconv, lintegral_map hf measurable_mul]

@[to_additive]
theorem lintegral_mconv [MeasurableMul₂ M] {μ ν : Measure M} [SFinite ν]
    {f : M → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ z, f z ∂(μ ∗ ν) = ∫⁻ x, ∫⁻ y, f (x * y) ∂ν ∂μ := by
  rw [lintegral_mconv_eq_lintegral_prod hf, lintegral_prod]
  fun_prop

/-- Convolution of the dirac measure at 1 with a measure μ returns μ. -/
@[to_additive (attr := simp) "Convolution of the dirac measure at 0 with a measure μ returns μ."]
theorem dirac_one_mconv [MeasurableMul₂ M] (μ : Measure M) [SFinite μ] :
    (Measure.dirac 1) ∗ μ = μ := by
  unfold mconv
  rw [MeasureTheory.Measure.dirac_prod, map_map (by fun_prop)]
  · simp only [Function.comp_def, one_mul, map_id']
  fun_prop

/-- Convolution of a measure μ with the dirac measure at 1 returns μ. -/
@[to_additive (attr := simp) "Convolution of a measure μ with the dirac measure at 0 returns μ."]
theorem mconv_dirac_one [MeasurableMul₂ M]
    (μ : Measure M) [SFinite μ] : μ ∗ (Measure.dirac 1) = μ := by
  unfold mconv
  rw [MeasureTheory.Measure.prod_dirac, map_map (by fun_prop)]
  · simp only [Function.comp_def, mul_one, map_id']
  fun_prop

/-- Convolution of the zero measure with a measure μ returns the zero measure. -/
@[to_additive (attr := simp) "Convolution of the zero measure with a measure μ returns
the zero measure."]
theorem zero_mconv (μ : Measure M) : (0 : Measure M) ∗ μ = (0 : Measure M) := by
  unfold mconv
  simp

/-- Convolution of a measure μ with the zero measure returns the zero measure. -/
@[to_additive (attr := simp) "Convolution of a measure μ with the zero measure returns the zero
measure."]
theorem mconv_zero (μ : Measure M) : μ ∗ (0 : Measure M) = (0 : Measure M) := by
  unfold mconv
  simp

@[to_additive]
theorem mconv_add [MeasurableMul₂ M] (μ : Measure M) (ν : Measure M) (ρ : Measure M) [SFinite μ]
    [SFinite ν] [SFinite ρ] : μ ∗ (ν + ρ) = μ ∗ ν + μ ∗ ρ := by
  unfold mconv
  rw [prod_add, Measure.map_add]
  fun_prop

@[to_additive]
theorem add_mconv [MeasurableMul₂ M] (μ : Measure M) (ν : Measure M) (ρ : Measure M) [SFinite μ]
    [SFinite ν] [SFinite ρ] : (μ + ν) ∗ ρ = μ ∗ ρ + ν ∗ ρ := by
  unfold mconv
  rw [add_prod, Measure.map_add]
  fun_prop

/-- To get commutativity, we need the underlying multiplication to be commutative. -/
@[to_additive "To get commutativity, we need the underlying addition to be commutative."]
theorem mconv_comm {M : Type*} [CommMonoid M] [MeasurableSpace M] [MeasurableMul₂ M] (μ : Measure M)
    (ν : Measure M) [SFinite μ] [SFinite ν] : μ ∗ ν = ν ∗ μ := by
  unfold mconv
  rw [← prod_swap, map_map (by fun_prop)]
  · simp [Function.comp_def, mul_comm]
  fun_prop

/-- The convolution of s-finite measures is s-finite. -/
@[to_additive "The convolution of s-finite measures is s-finite."]
instance sfinite_mconv_of_sfinite (μ : Measure M) (ν : Measure M) [SFinite μ] [SFinite ν] :
    SFinite (μ ∗ ν) := inferInstanceAs <| SFinite ((μ.prod ν).map fun (x : M × M) ↦ x.1 * x.2)

@[to_additive]
instance finite_of_finite_mconv (μ : Measure M) (ν : Measure M) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] : IsFiniteMeasure (μ ∗ ν) := by
  have h : (μ ∗ ν) Set.univ < ⊤ := by
    unfold mconv
    exact IsFiniteMeasure.measure_univ_lt_top
  exact {measure_univ_lt_top := h}

/-- Convolution is associative. -/
@[to_additive "Convolution is associative."]
theorem mconv_assoc [MeasurableMul₂ M] (μ ν ρ : Measure M)
    [SFinite ν] [SFinite ρ] :
    (μ ∗ ν) ∗ ρ = μ ∗ (ν ∗ ρ) := by
  refine ext_of_lintegral _ fun f hf ↦ ?_
  repeat rw [lintegral_mconv (by fun_prop)]
  refine lintegral_congr fun x ↦ ?_
  rw [lintegral_mconv (by fun_prop)]
  repeat refine lintegral_congr fun x ↦ ?_
  simp [mul_assoc]

@[to_additive]
instance probabilitymeasure_of_probabilitymeasures_mconv (μ : Measure M) (ν : Measure M)
    [MeasurableMul₂ M] [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (μ ∗ ν) :=
  MeasureTheory.isProbabilityMeasure_map (by fun_prop)

open ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]

@[to_additive]
theorem IndepFun.map_mul_eq_map_mconv_map [MeasurableMul₂ M]
    {f g : Ω → M} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) (hfg : IndepFun f g μ):
    μ.map (f * g) = (μ.map f) ∗ (μ.map g) := by
  conv in f * g => change (fun (x,y) ↦ x * y) ∘ (fun ω ↦ (f ω, g ω))
  rw [← measurable_mul.aemeasurable.map_map_of_aemeasurable (hf.prodMk hg),
     (indepFun_iff_map_prod_eq_prod_map_map hf hg).mp hfg]
  rfl

@[to_additive]
theorem IndepFun.map_fun_mul_eq_map_mconv_map
    [MeasurableMul₂ M] {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
    {f g : Ω → M} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) (hfg : IndepFun f g μ):
    μ.map (fun x ↦ f x * g x) = (μ.map f) ∗ (μ.map g) :=
  IndepFun.map_mul_eq_map_mconv_map hf hg hfg

section withDensity

variable {G : Type*} [Group G] {mG : MeasurableSpace G} [MeasurableMul₂ G] [MeasurableInv G]


variable {π : Measure G} [SFinite π] [IsMulLeftInvariant π]

@[to_additive]
theorem mconv_withDensity_eq_mlconvolution₀ {f g : G → ℝ≥0∞}
    (hf : AEMeasurable f π) (hg : AEMeasurable g π) :
    π.withDensity f ∗ π.withDensity g = π.withDensity (f ⋆ₗ[π] g) := by
  refine ext_of_lintegral _ fun φ hφ ↦ ?_
  rw [lintegral_mconv_eq_lintegral_prod hφ, prod_withDensity₀ hf hg,
    lintegral_withDensity_eq_lintegral_mul₀,
    lintegral_withDensity_eq_lintegral_mul₀, lintegral_prod,
    lintegral_congr (fun x ↦ by apply (lintegral_mul_left_eq_self _ x⁻¹).symm),
    lintegral_lintegral_swap]
  · simp only [Pi.mul_apply, mul_inv_cancel_left, mlconvolution_def]
    conv in (∫⁻ _ , _ ∂π) * φ _ => rw[(lintegral_mul_const'' _ (by fun_prop)).symm]
  all_goals first | fun_prop | simp; fun_prop

@[to_additive]
theorem mconv_withDensity_eq_mlconvolution {f g : G → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) :
    π.withDensity f ∗ π.withDensity g = π.withDensity (f ⋆ₗ[π] g) :=
  mconv_withDensity_eq_mlconvolution₀ hf.aemeasurable hg.aemeasurable

open pdf

-- probably should do an intermediary that works with rnderiv

@[to_additive]
theorem HasPDF.mul {μ : Measure Ω} [IsFiniteMeasure μ] {f g : Ω → G}
    (hfg : IndepFun f g μ) [hf : HasPDF f μ π] [hg : HasPDF g μ π] : HasPDF (f * g) μ π := by
  apply hasPDF_of_map_eq_withDensity _ ((pdf f μ π) ⋆ₗ[π] (pdf g μ π))
  · apply aemeasurable_mlconvolution
    repeat exact (measurable_pdf _ _ _).aemeasurable
  · rw[IndepFun.map_mul_eq_map_mconv_map hf.aemeasurable hg.aemeasurable hfg,
      ← mconv_withDensity_eq_mlconvolution₀,
      map_eq_withDensity_pdf f μ π, map_eq_withDensity_pdf g μ π]
    repeat exact (measurable_pdf _ _ _).aemeasurable
  exact (hf.aemeasurable).mul hg.aemeasurable

-- @[to_additive]
-- theorem IndepFun.map_mul_eq_pdf_mlconvolution {μ : Measure Ω} [IsFiniteMeasure μ]
--     {f g : Ω → G} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
--     (hfg : IndepFun f g μ) [HasPDF f μ π] [HasPDF g μ π] :
--     pdf (f * g) μ π =ᶠ[ae π] (pdf f μ π) ⋆ₗ[π] (pdf g μ π) := by
--   rw[← eq_of_map_eq_withDensity]

end withDensity

end Measure

end MeasureTheory
