/-
Copyright (c) 2025 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Convolution of functions using the Lebesgue integral

In this file we define and prove properties about the convolution of two functions
using the Lebesgue integral.

## Design Decisions

We define the convolution of two functions using the Lebesgue integral (in the additive case)
by the formula `(f ⋆ₗ[μ] g) x = ∫⁻ y, (f y) * (g (-y + x)) ∂μ`. This does not agree with the
formula used by `MeasureTheory.convolution` for convolution of two functions, however it does agree
when the domain of `f` and `g` is a commutative group. The main reason for this is so that
(under sufficient conditions) if `{μ ν π : Measure G} {f g : G → ℝ≥0∞}` are such that
`μ = π.withDensity f`, `ν = π.withDensity g` where `π` is left-invariant then
`(μ ∗ ν) = π.withDensity (f ⋆ₗ[π] g)`. If the formula in `MeasureTheory.convolution` was used
the order of the densities would be flipped.

## Main Definitions

* `MeasureTheory.mlconvolution f g μ x = (f ⋆ₗ[μ] g) x = ∫⁻ y, (f y) * (g (y⁻¹ * x)) ∂μ`
  is the multiplicative convolution of `f` and `g` w.r.t. the measure `μ`.
* `MeasureTheory.lconvolution f g μ x = (f ⋆ₗ[μ] g) x = ∫⁻ y, (f y) * (g (-y + x)) ∂μ`
  is the additive convolution of `f` and `g` w.r.t. the measure `μ`.
-/

namespace MeasureTheory
open Measure
open scoped ENNReal

variable {G : Type*} {mG : MeasurableSpace G} [Mul G] [Inv G]

/-- Multiplicative convolution of functions. -/
@[to_additive "Additive convolution of functions"]
noncomputable def mlconvolution (f g : G → ℝ≥0∞) (μ : Measure G) :
    G → ℝ≥0∞ := fun x ↦ ∫⁻ y, (f y) * (g (y⁻¹ * x)) ∂μ

/-- Scoped notation for the multiplicative convolution of functions with respect to a measure `μ`.
-/
scoped[MeasureTheory] notation:67 f " ⋆ₗ["μ:67"] " g:66 => MeasureTheory.mlconvolution f g μ

/-- Scoped notation for the multiplicative convolution of functions with respect to `volume`. -/
scoped[MeasureTheory] notation:67 f " ⋆ₗ " g:66 => MeasureTheory.mlconvolution f g volume

/-- Scoped notation for the additive convolution of functions with respect to a measure `μ`. -/
scoped[MeasureTheory] notation:67 f " ⋆ₗ["μ:67"] " g:66 => MeasureTheory.lconvolution f g μ

/-- Scoped notation for the additive convolution of functions with respect to `volume`. -/
scoped[MeasureTheory] notation:67 f " ⋆ₗ " g:66 => MeasureTheory.lconvolution f g volume

/- The definition of multiplicative convolution of functions. -/
@[to_additive "The definition of additive convolution of functions."]
theorem mlconvolution_def {f g : G → ℝ≥0∞} {μ : Measure G} {x : G}:
    (f ⋆ₗ[μ] g) x = ∫⁻ y, (f y) * (g (y⁻¹ * x)) ∂μ := rfl

/-- Convolution of the zero function with a function returns the zero function. -/
@[to_additive (attr := simp)
"Convolution of the zero function with a function returns the zero function."]
theorem zero_mlconvolution (f : G → ℝ≥0∞) (μ : Measure G) : 0 ⋆ₗ[μ] f = 0 := by
  ext; simp [mlconvolution]

/-- Convolution of a function with the zero function returns the zero function. -/
@[to_additive (attr := simp)
"Convolution of a function with the zero function returns the zero function."]
theorem mlconvolution_zero (f : G → ℝ≥0∞) (μ : Measure G) : f ⋆ₗ[μ] 0 = 0 := by
  ext; simp [mlconvolution]

/-- The convolution of measurable functions is measurable. -/
@[to_additive (attr := measurability, fun_prop)
"The convolution of measurable functions is measurable."]
theorem measurable_mlconvolution [MeasurableMul₂ G] [MeasurableInv G]
    {f g : G → ℝ≥0∞} (μ : Measure G) [SFinite μ]
    (hf : Measurable f) (hg : Measurable g) : Measurable (f ⋆ₗ[μ] g) := by
  apply Measurable.lintegral_prod_right
  fun_prop

end MeasureTheory
