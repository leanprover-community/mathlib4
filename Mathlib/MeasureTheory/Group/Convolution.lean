/-
Copyright (c) 2023 Josha Dekker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josha Dekker
-/
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.LConvolution
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Probability.Independence.Basic
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
@[to_additive conv "Additive convolution of measures."]
noncomputable def mconv (μ : Measure M) (ν : Measure M) :
    Measure M := Measure.map (fun x : M × M ↦ x.1 * x.2) (μ.prod ν)

/-- Scoped notation for the multiplicative convolution of measures. -/
scoped[MeasureTheory] infix:80 " ∗ " => MeasureTheory.Measure.mconv

/-- Scoped notation for the additive convolution of measures. -/
scoped[MeasureTheory] infix:80 " ∗ " => MeasureTheory.Measure.conv

@[to_additive lintegral_conv]
theorem lintegral_mconv [MeasurableMul₂ M] {μ : Measure M} {ν : Measure M} [SFinite ν]
    {f : M → ℝ≥0∞} (hf : Measurable f):
    ∫⁻ z, f z ∂(μ ∗ ν) = ∫⁻ x, ∫⁻ y, f (x * y) ∂ν ∂μ := by
  rw[mconv, lintegral_map hf measurable_mul, lintegral_prod]
  fun_prop

/-- Convolution of the dirac measure at 1 with a measure μ returns μ. -/
@[to_additive (attr := simp)]
theorem dirac_one_mconv [MeasurableMul₂ M] (μ : Measure M) [SFinite μ] :
    (Measure.dirac 1) ∗ μ = μ := by
  unfold mconv
  rw [MeasureTheory.Measure.dirac_prod, map_map (by fun_prop)]
  · simp only [Function.comp_def, one_mul, map_id']
  fun_prop

/-- Convolution of a measure μ with the dirac measure at 1 returns μ. -/
@[to_additive (attr := simp)]
theorem mconv_dirac_one [MeasurableMul₂ M]
    (μ : Measure M) [SFinite μ] : μ ∗ (Measure.dirac 1) = μ := by
  unfold mconv
  rw [MeasureTheory.Measure.prod_dirac, map_map (by fun_prop)]
  · simp only [Function.comp_def, mul_one, map_id']
  fun_prop

/-- Convolution of the zero measure with a measure μ returns the zero measure. -/
@[to_additive (attr := simp) zero_conv]
theorem zero_mconv (μ : Measure M) : (0 : Measure M) ∗ μ = (0 : Measure M) := by
  unfold mconv
  simp

/-- Convolution of a measure μ with the zero measure returns the zero measure. -/
@[to_additive (attr := simp) conv_zero]
theorem mconv_zero (μ : Measure M) : μ ∗ (0 : Measure M) = (0 : Measure M) := by
  unfold mconv
  simp

@[to_additive conv_add]
theorem mconv_add [MeasurableMul₂ M] (μ : Measure M) (ν : Measure M) (ρ : Measure M) [SFinite μ]
    [SFinite ν] [SFinite ρ] : μ ∗ (ν + ρ) = μ ∗ ν + μ ∗ ρ := by
  unfold mconv
  rw [prod_add, map_add]
  fun_prop

@[to_additive add_conv]
theorem add_mconv [MeasurableMul₂ M] (μ : Measure M) (ν : Measure M) (ρ : Measure M) [SFinite μ]
    [SFinite ν] [SFinite ρ] : (μ + ν) ∗ ρ = μ ∗ ρ + ν ∗ ρ := by
  unfold mconv
  rw [add_prod, map_add]
  fun_prop

/-- To get commutativity, we need the underlying multiplication to be commutative. -/
@[to_additive conv_comm]
theorem mconv_comm {M : Type*} [CommMonoid M] [MeasurableSpace M] [MeasurableMul₂ M] (μ : Measure M)
    (ν : Measure M) [SFinite μ] [SFinite ν] : μ ∗ ν = ν ∗ μ := by
  unfold mconv
  rw [← prod_swap, map_map (by fun_prop)]
  · simp [Function.comp_def, mul_comm]
  fun_prop

/-- Convolution of SFinite maps is SFinite. -/
@[to_additive sfinite_conv_of_sfinite]
instance sfinite_mconv_of_sfinite (μ : Measure M) (ν : Measure M) [SFinite μ] [SFinite ν] :
    SFinite (μ ∗ ν) := inferInstanceAs <| SFinite ((μ.prod ν).map fun (x : M × M) ↦ x.1 * x.2)

@[to_additive finite_of_finite_conv]
instance finite_of_finite_mconv (μ : Measure M) (ν : Measure M) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] : IsFiniteMeasure (μ ∗ ν) := by
  have h : (μ ∗ ν) Set.univ < ⊤ := by
    unfold mconv
    exact IsFiniteMeasure.measure_univ_lt_top
  exact {measure_univ_lt_top := h}

/-- Convolution is associative -/
@[to_additive conv_assoc]
theorem mconv_assoc [MeasurableMul₂ M] (μ : Measure M) (ν : Measure M) (ρ : Measure M)
    [SFinite ν] [SFinite ρ] :
    (μ ∗ ν) ∗ ρ = μ ∗ (ν ∗ ρ) := by
  rw[measure_eq_measure_iff_lintegral_eq_lintegral]
  intro f hf
  repeat rw[lintegral_mconv (by first | fun_prop | apply Measurable.lintegral_prod_right; fun_prop)]
  refine lintegral_congr (fun x ↦ ?_)
  rw[lintegral_mconv (by fun_prop)]
  repeat refine lintegral_congr (fun x ↦ ?_)
  apply congr_arg
  simp [mul_assoc]

@[to_additive probabilitymeasure_of_probabilitymeasures_conv]
instance probabilitymeasure_of_probabilitymeasures_mconv (μ : Measure M) (ν : Measure M)
    [MeasurableMul₂ M] [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (μ ∗ ν) :=
  MeasureTheory.isProbabilityMeasure_map (by fun_prop)

section Group

variable {G : Type*} [Group G] [MeasurableSpace G]
         {π : Measure G} [SFinite π] [IsMulLeftInvariant π]

@[to_additive conv_withDensity_lconvolution]
theorem mconv_withDensity_mlconvolution
    [MeasurableMul₂ G] [MeasurableInv G] {μ : Measure G} {ν : Measure G} [SFinite ν]
    {f : G → ℝ≥0∞} {g : G → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    (hμ : μ = π.withDensity f) (hν : ν = π.withDensity g):
    (μ ∗ ν) = π.withDensity (f ⋆ₗ[π] g) := by
  rw[measure_eq_measure_iff_lintegral_eq_lintegral]
  intro h mh
  rw[mconv, lintegral_map' (by fun_prop) (by fun_prop), prod_withDensity_mul hf hg hμ hν,
     lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop),
     lintegral_withDensity_eq_lintegral_mul _ (by apply mlconvolution_measurable hf hg)
     (by fun_prop), lintegral_prod _ (by fun_prop),
     lintegral_congr (fun x ↦ by apply (lintegral_mul_left_eq_self _ x⁻¹).symm),
     lintegral_lintegral_swap (by fun_prop)]
  simp[mlconvolution_def]
  conv =>
    rhs
    rw [lintegral_congr (fun x ↦ by apply (lintegral_mul_const (h x) (by fun_prop)).symm)]

end Group

end Measure

end MeasureTheory
