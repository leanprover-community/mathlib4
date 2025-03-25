/-
Copyright (c) 2025 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Convolution of functions using the Lebesgue Integral

In this file we define and prove properties about the convolution of two functions on a group
using the lebesgue integral.

# Main Definitions

* `MeasureTheory.mlconvolution f g μ x = (f ⋆ₗ[μ] g) x = ∫⁻ y, (f y) * (g (y⁻¹ * x)) ∂μ`
  is multiplicative convolution of `f` and `g` w.r.t to the measure `μ`
* `MeasureTheory.lconvolution f g μ x = (f ⋆ₗ[μ] g) x = ∫⁻ y, (f y) * (g (-y + x)) ∂μ`
  is additive convolution of `f` and `g` w.r.t to the measure `μ`
-/

namespace MeasureTheory
open Measure
open scoped ENNReal
--open Measure

variable {G : Type*} [Group G] [MeasurableSpace G]

/-- Multiplicative convolution of functions -/
@[to_additive lconvolution "Additive convolution of functions"]
noncomputable def mlconvolution (f : G → ℝ≥0∞) (g : G → ℝ≥0∞) (μ : Measure G := by volume_tac):
    G → ℝ≥0∞ := fun x ↦ ∫⁻ y, (f y) * (g (y⁻¹ * x)) ∂μ

/-- Scoped notation for the multiplicative convolution of functions with respect to a measure `μ` -/
scoped[MeasureTheory] notation:66 f " ⋆ₗ["μ:67"] " g:67  => MeasureTheory.mlconvolution f g μ

/-- Scoped notation for the multiplicative convolution of functions with respect to volume -/
scoped[MeasureTheory] notation:66 f " ⋆ₗ " g:67  => MeasureTheory.mlconvolution f g

/-- Scoped notation for the additive convolution of functions with respect to a measure `μ` -/
scoped[MeasureTheory] notation:66 f " ⋆ₗ["μ:67"]" g:67  => MeasureTheory.lconvolution f g μ

/-- Scoped notation for the additive convolution of functions with respect to volume -/
scoped[MeasureTheory] notation:66 f " ⋆ₗ " g:67  => MeasureTheory.lconvolution f g

/- The definition of multiplicative convolution of functions -/
@[to_additive lconvolution_def "The definition of additive convolution of functions"]
theorem mlconvolution_def {f : G → ℝ≥0∞} {g : G → ℝ≥0∞} {μ : Measure G} {x : G}:
    (f ⋆ₗ[μ] g) x = ∫⁻ y, (f y) * (g (y⁻¹ * x)) ∂μ := by rfl

/-- Convolution of the zero function with a function returns the zero function -/
@[to_additive zero_lconvolution]
theorem zero_mlconvolution (f : G → ℝ≥0∞) (μ : Measure G) : 0 ⋆ₗ[μ] f = 0 := by
  unfold mlconvolution
  simp
  rfl

/-- Convolution with the zero function with a function returns the zero function -/
@[to_additive lconvolution_zero]
theorem mlconvolution_zero (f : G → ℝ≥0∞) (μ : Measure G) : f ⋆ₗ[μ] 0 = 0 := by
  unfold mlconvolution
  simp
  rfl

/-- The convolution of measurable functions is measurable -/
@[to_additive lconvolution_measurable]
theorem mlconvolution_measurable [MeasurableMul₂ G] [MeasurableInv G]
    {f : G → ℝ≥0∞} {g : G → ℝ≥0∞} (μ : Measure G) [SFinite μ]
    (hf : Measurable f) (hg : Measurable g) : Measurable (f ⋆ₗ[μ] g) := by
  unfold mlconvolution
  apply Measurable.lintegral_prod_right
  fun_prop

/- Test Comment -/

end MeasureTheory
