/-
Copyright (c) 2025 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.MeasureTheory.Group.Prod
public import Mathlib.MeasureTheory.Group.LIntegral

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

* `MeasureTheory.mlconvolution f g μ x = (f ⋆ₘₗ[μ] g) x = ∫⁻ y, (f y) * (g (y⁻¹ * x)) ∂μ`
  is the multiplicative convolution of `f` and `g` w.r.t. the measure `μ`.
* `MeasureTheory.lconvolution f g μ x = (f ⋆ₗ[μ] g) x = ∫⁻ y, (f y) * (g (-y + x)) ∂μ`
  is the additive convolution of `f` and `g` w.r.t. the measure `μ`.
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

namespace MeasureTheory
open Measure
open scoped ENNReal

variable {G : Type*} {mG : MeasurableSpace G}

section NoGroup

variable [Mul G] [Inv G]

/-- Multiplicative convolution of functions. -/
@[to_additive /-- Additive convolution of functions -/]
noncomputable def mlconvolution (f g : G → ℝ≥0∞) (μ : Measure G) :
    G → ℝ≥0∞ := fun x ↦ ∫⁻ y, (f y) * (g (y⁻¹ * x)) ∂μ

/-- Scoped notation for the multiplicative convolution of functions with respect to a measure `μ`.
-/
scoped[MeasureTheory] notation:67 f " ⋆ₘₗ[" μ:67 "] " g:66 => MeasureTheory.mlconvolution f g μ

/-- Scoped notation for the multiplicative convolution of functions with respect to `volume`. -/
scoped[MeasureTheory] notation:67 f " ⋆ₘₗ " g:66 => MeasureTheory.mlconvolution f g volume

/-- Scoped notation for the additive convolution of functions with respect to a measure `μ`. -/
scoped[MeasureTheory] notation:67 f " ⋆ₗ[" μ:67 "] " g:66 => MeasureTheory.lconvolution f g μ

/-- Scoped notation for the additive convolution of functions with respect to `volume`. -/
scoped[MeasureTheory] notation:67 f " ⋆ₗ " g:66 => MeasureTheory.lconvolution f g volume

/- The definition of multiplicative convolution of functions. -/
@[to_additive /-- The definition of additive convolution of functions. -/]
theorem mlconvolution_def {f g : G → ℝ≥0∞} {μ : Measure G} {x : G} :
    (f ⋆ₘₗ[μ] g) x = ∫⁻ y, (f y) * (g (y⁻¹ * x)) ∂μ := rfl

/-- Convolution of the zero function with a function returns the zero function. -/
@[to_additive (attr := simp)
/-- Convolution of the zero function with a function returns the zero function. -/]
theorem zero_mlconvolution (f : G → ℝ≥0∞) (μ : Measure G) : 0 ⋆ₘₗ[μ] f = 0 := by
  ext; simp [mlconvolution]

/-- Convolution of a function with the zero function returns the zero function. -/
@[to_additive (attr := simp)
/-- Convolution of a function with the zero function returns the zero function. -/]
theorem mlconvolution_zero (f : G → ℝ≥0∞) (μ : Measure G) : f ⋆ₘₗ[μ] 0 = 0 := by
  ext; simp [mlconvolution]

section Measurable

variable [MeasurableMul₂ G] [MeasurableInv G]

/-- The convolution of measurable functions is measurable. -/
@[to_additive (attr := fun_prop)
/-- The convolution of measurable functions is measurable. -/]
theorem measurable_mlconvolution {f g : G → ℝ≥0∞} (μ : Measure G) [SFinite μ]
    (hf : Measurable f) (hg : Measurable g) : Measurable (f ⋆ₘₗ[μ] g) := by
  unfold mlconvolution
  fun_prop

end Measurable

end NoGroup

section Group

variable [Group G] [MeasurableMul₂ G] [MeasurableInv G]

variable {μ : Measure G} [IsMulLeftInvariant μ] [SFinite μ]

/-- The convolution of `AEMeasurable` functions is `AEMeasurable`. -/
@[to_additive (attr := fun_prop)
/-- The convolution of `AEMeasurable` functions is `AEMeasurable`. -/]
theorem aemeasurable_mlconvolution {f g : G → ℝ≥0∞}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    AEMeasurable (f ⋆ₘₗ[μ] g) μ := by
  unfold mlconvolution
  fun_prop

@[to_additive]
theorem mlconvolution_assoc₀ {f g k : G → ℝ≥0∞}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) (hk : AEMeasurable k μ) :
    f ⋆ₘₗ[μ] g ⋆ₘₗ[μ] k = (f ⋆ₘₗ[μ] g) ⋆ₘₗ[μ] k := by
  ext x
  simp only [mlconvolution_def]
  conv in f _ * (∫⁻ _, _ ∂μ) =>
    rw [← lintegral_const_mul'' _ (by fun_prop), ← lintegral_mul_left_eq_self _ y⁻¹]
  conv in (∫⁻ _, _ ∂μ) * k _ =>
    rw [← lintegral_mul_const'' _ (by fun_prop)]
  rw [lintegral_lintegral_swap]
  · simp [mul_assoc]
  simpa [mul_assoc] using by fun_prop

/- Convolution is associative. -/
@[to_additive /-- Convolution is associative. -/]
theorem mlconvolution_assoc {f g k : G → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (hk : Measurable k) :
    f ⋆ₘₗ[μ] g ⋆ₘₗ[μ] k = (f ⋆ₘₗ[μ] g) ⋆ₘₗ[μ] k :=
  mlconvolution_assoc₀ hf.aemeasurable hg.aemeasurable hk.aemeasurable

end Group

section CommGroup

variable [CommGroup G] [MeasurableMul₂ G] [MeasurableInv G] {μ : Measure G}

/-- Convolution is commutative when the group is commutative. -/
@[to_additive /-- Convolution is commutative when the group is commutative. -/]
theorem mlconvolution_comm [IsMulLeftInvariant μ] [IsInvInvariant μ] {f g : G → ℝ≥0∞} :
    (f ⋆ₘₗ[μ] g) = (g ⋆ₘₗ[μ] f) := by
  ext x
  simp only [mlconvolution_def]
  rw [← lintegral_mul_left_eq_self _ x, ← lintegral_inv_eq_self]
  simp [mul_comm]

end CommGroup

end MeasureTheory
