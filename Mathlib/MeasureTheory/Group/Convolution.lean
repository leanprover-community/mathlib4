/-
Copyright (c) 2023 Josha Dekker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josha Dekker
-/
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Prod

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
@[to_additive /-- Additive convolution of measures. -/]
noncomputable def mconv (μ : Measure M) (ν : Measure M) :
    Measure M := Measure.map (fun x : M × M ↦ x.1 * x.2) (μ.prod ν)

/-- Scoped notation for the multiplicative convolution of measures. -/
scoped[MeasureTheory] infixr:80 " ∗ₘ " => MeasureTheory.Measure.mconv

/-- Scoped notation for the additive convolution of measures. -/
scoped[MeasureTheory] infixr:80 " ∗ " => MeasureTheory.Measure.conv

@[to_additive]
theorem lintegral_mconv_eq_lintegral_prod [MeasurableMul₂ M] {μ ν : Measure M}
    {f : M → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ z, f z ∂(μ ∗ₘ ν) = ∫⁻ z, f (z.1 * z.2) ∂(μ.prod ν) := by
  rw [mconv, lintegral_map hf measurable_mul]

@[to_additive]
theorem lintegral_mconv [MeasurableMul₂ M] {μ ν : Measure M} [SFinite ν]
    {f : M → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ z, f z ∂(μ ∗ₘ ν) = ∫⁻ x, ∫⁻ y, f (x * y) ∂ν ∂μ := by
  rw [lintegral_mconv_eq_lintegral_prod hf, lintegral_prod _ (by fun_prop)]

@[to_additive]
lemma dirac_mconv [MeasurableMul₂ M] (x : M) (μ : Measure M) [SFinite μ] :
    (Measure.dirac x) ∗ₘ μ = μ.map (fun y ↦ x * y) := by
  unfold mconv
  rw [Measure.dirac_prod, map_map (by fun_prop) (by fun_prop)]
  simp [Function.comp_def]

@[to_additive]
lemma mconv_dirac [MeasurableMul₂ M] (μ : Measure M) [SFinite μ] (x : M) :
    μ ∗ₘ (Measure.dirac x) = μ.map (fun y ↦ y * x) := by
  unfold mconv
  rw [Measure.prod_dirac, map_map (by fun_prop) (by fun_prop)]
  simp [Function.comp_def]

/-- Convolution of the dirac measure at 1 with a measure μ returns μ. -/
@[to_additive (attr := simp)
/-- Convolution of the dirac measure at 0 with a measure μ returns μ. -/]
theorem dirac_one_mconv [MeasurableMul₂ M] (μ : Measure M) [SFinite μ] :
    (Measure.dirac 1) ∗ₘ μ = μ := by
  simp [dirac_mconv]

/-- Convolution of a measure μ with the dirac measure at 1 returns μ. -/
@[to_additive (attr := simp)
/-- Convolution of a measure μ with the dirac measure at 0 returns μ. -/]
theorem mconv_dirac_one [MeasurableMul₂ M]
    (μ : Measure M) [SFinite μ] : μ ∗ₘ (Measure.dirac 1) = μ := by
  simp [mconv_dirac]

/-- Convolution of the zero measure with a measure μ returns the zero measure. -/
@[to_additive (attr := simp) /-- Convolution of the zero measure with a measure μ returns
the zero measure. -/]
theorem zero_mconv (μ : Measure M) : (0 : Measure M) ∗ₘ μ = (0 : Measure M) := by
  unfold mconv
  simp

/-- Convolution of a measure μ with the zero measure returns the zero measure. -/
@[to_additive (attr := simp) /-- Convolution of a measure μ with the zero measure returns the zero
measure. -/]
theorem mconv_zero (μ : Measure M) : μ ∗ₘ (0 : Measure M) = (0 : Measure M) := by
  unfold mconv
  simp

@[to_additive]
theorem mconv_add [MeasurableMul₂ M] (μ : Measure M) (ν : Measure M) (ρ : Measure M) [SFinite μ]
    [SFinite ν] [SFinite ρ] : μ ∗ₘ (ν + ρ) = μ ∗ₘ ν + μ ∗ₘ ρ := by
  unfold mconv
  rw [prod_add, Measure.map_add]
  fun_prop

@[to_additive]
theorem add_mconv [MeasurableMul₂ M] (μ : Measure M) (ν : Measure M) (ρ : Measure M) [SFinite μ]
    [SFinite ν] [SFinite ρ] : (μ + ν) ∗ₘ ρ = μ ∗ₘ ρ + ν ∗ₘ ρ := by
  unfold mconv
  rw [add_prod, Measure.map_add]
  fun_prop

/-- To get commutativity, we need the underlying multiplication to be commutative. -/
@[to_additive /-- To get commutativity, we need the underlying addition to be commutative. -/]
theorem mconv_comm {M : Type*} [CommMonoid M] [MeasurableSpace M] [MeasurableMul₂ M] (μ : Measure M)
    (ν : Measure M) [SFinite μ] [SFinite ν] : μ ∗ₘ ν = ν ∗ₘ μ := by
  unfold mconv
  rw [← prod_swap, map_map (by fun_prop)]
  · simp [Function.comp_def, mul_comm]
  fun_prop

/-- The convolution of s-finite measures is s-finite. -/
@[to_additive /-- The convolution of s-finite measures is s-finite. -/]
instance sfinite_mconv_of_sfinite (μ : Measure M) (ν : Measure M) [SFinite μ] [SFinite ν] :
    SFinite (μ ∗ₘ ν) := inferInstanceAs <| SFinite ((μ.prod ν).map fun (x : M × M) ↦ x.1 * x.2)

@[to_additive]
instance finite_of_finite_mconv (μ : Measure M) (ν : Measure M) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] : IsFiniteMeasure (μ ∗ₘ ν) := by
  have h : (μ ∗ₘ ν) Set.univ < ⊤ := by
    unfold mconv
    exact IsFiniteMeasure.measure_univ_lt_top
  exact {measure_univ_lt_top := h}

/-- Convolution is associative. -/
@[to_additive /-- Convolution is associative. -/]
theorem mconv_assoc [MeasurableMul₂ M] (μ ν ρ : Measure M)
    [SFinite ν] [SFinite ρ] :
    (μ ∗ₘ ν) ∗ₘ ρ = μ ∗ₘ (ν ∗ₘ ρ) := by
  refine ext_of_lintegral _ fun f hf ↦ ?_
  repeat rw [lintegral_mconv (by fun_prop)]
  refine lintegral_congr fun x ↦ ?_
  rw [lintegral_mconv (by fun_prop)]
  repeat refine lintegral_congr fun x ↦ ?_
  simp [mul_assoc]

@[to_additive]
instance probabilitymeasure_of_probabilitymeasures_mconv (μ : Measure M) (ν : Measure M)
    [MeasurableMul₂ M] [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (μ ∗ₘ ν) :=
  MeasureTheory.isProbabilityMeasure_map (by fun_prop)

@[to_additive]
lemma map_mconv_monoidHom {M M' : Type*} {mM : MeasurableSpace M} [Monoid M] [MeasurableMul₂ M]
    {mM' : MeasurableSpace M'} [Monoid M'] [MeasurableMul₂ M']
    {μ ν : Measure M} [SFinite μ] [SFinite ν]
    (L : M →* M') (hL : Measurable L) :
    (μ ∗ₘ ν).map L = (μ.map L) ∗ₘ (ν.map L) := by
  unfold Measure.mconv
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  have : (L ∘ fun p : M × M ↦ p.1 * p.2) = (fun p : M' × M' ↦ p.1 * p.2) ∘ (Prod.map L L) := by
    ext; simp
  rw [this, ← Measure.map_map (by fun_prop) (by fun_prop),
    ← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop)]

lemma map_conv_continuousLinearMap {E F : Type*} [AddCommMonoid E] [AddCommMonoid F]
    [Module ℝ E] [Module ℝ F] [TopologicalSpace E] [TopologicalSpace F]
    {mE : MeasurableSpace E} [MeasurableAdd₂ E] {mF : MeasurableSpace F} [MeasurableAdd₂ F]
    [OpensMeasurableSpace E] [BorelSpace F]
    {μ ν : Measure E} [SFinite μ] [SFinite ν]
    (L : E →L[ℝ] F) :
    (μ ∗ ν).map L = (μ.map L) ∗ (ν.map L) := by
  suffices (μ ∗ ν).map (L : E →+ F) = (μ.map (L : E →+ F)) ∗ (ν.map (L : E →+ F)) by simpa
  rw [map_conv_addMonoidHom]
  rw [AddMonoidHom.coe_coe]
  fun_prop

end Measure

end MeasureTheory
