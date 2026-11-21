/-
Copyright (c) 2026 Kacper Proniewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kacper
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.WithDensity

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Covering.DensityTheorem
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# The Gauss map and the Gauss measure

The *Gauss map* is the map `x ↦ fract (1 / x)` on the unit interval. It acts as a shift on
continued fraction expansions: if `x = [0; a₁, a₂, a₃, …]` then `gaussMap x = [0; a₂, a₃, …]`.

The *Gauss measure* is the probability measure on `[0, 1]` with density
`x ↦ 1 / (log 2 * (1 + x))` with respect to the Lebesgue measure. It is invariant under the
Gauss map (and the Gauss map is in fact ergodic with respect to it).

## Main definitions

* `gaussMap`: the Gauss map `x ↦ Int.fract x⁻¹`. Note that `gaussMap 0 = 0` since `0⁻¹ = 0`.
* `gaussDensity`: the density `x ↦ (log 2)⁻¹ * (1 + x)⁻¹` of the Gauss measure.
* `gaussMeasure`: the Gauss measure on `ℝ`, supported on the unit interval.

## Main statements

* `measurable_gaussMap`: the Gauss map is measurable.
* `gaussMap_mem_Ico`: the Gauss map sends `ℝ` into `[0, 1)`.
* `gaussMeasure.instIsProbabilityMeasure`: the Gauss measure is a probability measure.

-/

@[expose] public section

open MeasureTheory Set Real

open scoped ENNReal

/-- The Gauss map `x ↦ fract (1 / x)`. By the convention `0⁻¹ = 0`, we have `gaussMap 0 = 0`. -/
noncomputable def gaussMap (x : ℝ) : ℝ := Int.fract x⁻¹

theorem gaussMap_apply (x : ℝ) : gaussMap x = Int.fract x⁻¹ := rfl

@[simp]
theorem gaussMap_zero : gaussMap 0 = 0 := by simp [gaussMap]

theorem gaussMap_mem_Ico (x : ℝ) : gaussMap x ∈ Ico 0 1 :=
  ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

@[fun_prop]
theorem measurable_gaussMap : Measurable gaussMap :=
  measurable_inv.fract

theorem mapsTo_gaussMap : MapsTo gaussMap (Ico 0 1) (Ico 0 1) :=
  fun x _ ↦ gaussMap_mem_Ico x

/-- The density `x ↦ 1 / (log 2 * (1 + x))` of the Gauss measure with respect to the Lebesgue
measure on the unit interval. -/
noncomputable def gaussDensity (x : ℝ) : ℝ := (log 2)⁻¹ * (1 + x)⁻¹

theorem gaussDensity_pos {x : ℝ} (hx : -1 < x) : 0 < gaussDensity x := by
  unfold gaussDensity
  have := log_pos one_lt_two
  have : 0 < 1 + x := by linarith
  positivity

@[fun_prop]
theorem measurable_gaussDensity : Measurable gaussDensity := by
  unfold gaussDensity
  fun_prop

theorem continuousOn_gaussDensity : ContinuousOn gaussDensity (Ioi (-1)) := by
  unfold gaussDensity
  have h : ContinuousOn (fun x : ℝ => (1 + x)⁻¹) (Ioi (-1)) := by
    apply ContinuousOn.inv₀
    · fun_prop
    · intro x hx
      have h1 : (-1 : ℝ) < x := hx
      linarith
  apply continuousOn_const.mul h

theorem integral_gaussDensity : ∫ x in (0 : ℝ)..1, gaussDensity x = 1 := by
  simp only [gaussDensity, intervalIntegral.integral_const_mul]
  have h : ∫ x in (0 : ℝ)..1, (1 + x)⁻¹ = Real.log 2 := by
    rw [intervalIntegral.integral_comp_add_left, integral_inv_of_pos (by norm_num) (by norm_num)]
    norm_num
  norm_num

/-- The Gauss measure: the measure on `ℝ` supported on the unit interval with density
`x ↦ 1 / (log 2 * (1 + x))` with respect to the Lebesgue measure. -/
noncomputable def gaussMeasure : Measure ℝ :=
  (volume.restrict (Ioo 0 1)).withDensity fun x ↦ ENNReal.ofReal (gaussDensity x)

namespace gaussMeasure

theorem gaussMeasure_apply {s : Set ℝ} (hs : MeasurableSet s) :
    gaussMeasure s = ∫⁻ x in s ∩ Ioo 0 1, ENNReal.ofReal (gaussDensity x) := by
  rw [gaussMeasure, withDensity_apply _ hs, Measure.restrict_restrict hs]

theorem gaussMeasure_apply_compl_Ioo : gaussMeasure (Ioo 0 1)ᶜ = 0 := by
  rw [gaussMeasure_apply measurableSet_Ioo.compl, compl_inter_self, Measure.restrict_empty,
    lintegral_zero_measure]

instance : IsProbabilityMeasure gaussMeasure := by
  constructor
  rw [gaussMeasure_apply MeasurableSet.univ, univ_inter, ← ofReal_integral_eq_lintegral_ofReal,
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    integral_gaussDensity, ENNReal.ofReal_one]
  · refine (ContinuousOn.integrableOn_Icc (a := 0) (b := 1) ?_).mono_set Ioo_subset_Icc_self
    exact continuousOn_gaussDensity.mono fun x hx ↦ show -1 < x by linarith [hx.1]
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact (gaussDensity_pos (by linarith [hx.1])).le

end gaussMeasure
