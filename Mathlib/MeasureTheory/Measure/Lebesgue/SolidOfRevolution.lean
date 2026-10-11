/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Volume of solids of revolution

We compute the volume of the solid obtained by rotating the region below the graph of a function
around an axis, in `ℝ × EuclideanSpace ℝ (Fin 2)`.

## Main statements

* `MeasureTheory.Measure.prod_setOf_mem_closedBall`: Cavalieri's principle for a region of a
  product whose slices are closed balls.
* `EuclideanSpace.volume_solidOfRevolution`: the solid obtained by rotating the region below the
  graph of a nonnegative continuous function `f` on `[a, b]` has volume `π ∫ₐᵇ f(x)² dx`.
* `EuclideanSpace.volume_cone`: a cone of radius `R` and height `H` has volume `π R² H / 3`.
-/

public section

open MeasureTheory Metric Set
open scoped ENNReal Real

namespace MeasureTheory.Measure

variable {α E : Type*} [MeasurableSpace α] [PseudoMetricSpace E] [MeasurableSpace E]
  [OpensMeasurableSpace E] {μ : Measure α} {ν : Measure E} [SFinite ν]

/-- **Cavalieri's principle** for a region whose slices are balls: the measure of
`{(x, y) | x ∈ s, y ∈ closedBall c (r x)}` is the integral over `s` of the measures of the
balls. -/
theorem prod_setOf_mem_closedBall {s : Set α} (hs : MeasurableSet s) {r : α → ℝ}
    (hr : Measurable r) (c : E) :
    μ.prod ν {p : α × E | p.1 ∈ s ∧ p.2 ∈ closedBall c (r p.1)} =
      ∫⁻ x in s, ν (closedBall c (r x)) ∂μ := by
  have hm : MeasurableSet {p : α × E | p.1 ∈ s ∧ p.2 ∈ closedBall c (r p.1)} :=
    (measurable_fst hs).inter <| measurableSet_le
      ((continuous_id.dist continuous_const).measurable.comp measurable_snd)
      (hr.comp measurable_fst)
  rw [prod_apply hm, ← lintegral_indicator hs]
  congr 1
  ext x
  by_cases hx : x ∈ s <;> simp [hx, Set.preimage, closedBall]

end MeasureTheory.Measure

namespace EuclideanSpace

/-- The volume of the solid obtained by rotating the region below the graph of `r` over `s`
around the first axis of `ℝ × ℝ²`. -/
theorem volume_setOf_mem_norm_le {s : Set ℝ} (hs : MeasurableSet s) {r : ℝ → ℝ}
    (hr : Measurable r) :
    volume {p : ℝ × EuclideanSpace ℝ (Fin 2) | p.1 ∈ s ∧ ‖p.2‖ ≤ r p.1} =
      ∫⁻ x in s, ENNReal.ofReal (r x) ^ 2 * ENNReal.ofReal π := by
  simp_rw [← mem_closedBall_zero_iff]
  rw [Measure.volume_eq_prod, Measure.prod_setOf_mem_closedBall hs hr]
  simp

/-- **Volume of a solid of revolution**: rotating the region below the graph of a nonnegative
continuous function `f` on `[a, b]` around the first axis gives a solid of volume
`π ∫ₐᵇ f(x)² dx`. -/
theorem volume_solidOfRevolution {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) (hf₀ : ∀ x ∈ Icc a b, 0 ≤ f x) :
    volume {p : ℝ × EuclideanSpace ℝ (Fin 2) | p.1 ∈ Icc a b ∧ ‖p.2‖ ≤ f p.1} =
      ENNReal.ofReal (π * ∫ x in a..b, f x ^ 2) := by
  -- only the values of `f` on `[a, b]` matter, so we may replace it by a measurable function
  set g : ℝ → ℝ := (Icc a b).piecewise f 0
  have hset : {p : ℝ × EuclideanSpace ℝ (Fin 2) | p.1 ∈ Icc a b ∧ ‖p.2‖ ≤ f p.1} =
      {p | p.1 ∈ Icc a b ∧ ‖p.2‖ ≤ g p.1} := by
    ext p
    simp +contextual [g]
  have hg : Measurable g := hf.measurable_piecewise continuousOn_const measurableSet_Icc
  rw [hset, volume_setOf_mem_norm_le measurableSet_Icc hg, intervalIntegral.integral_of_le hab,
    ← integral_Icc_eq_integral_Ioc, ← integral_const_mul,
    ofReal_integral_eq_lintegral_ofReal]
  · refine setLIntegral_congr_fun measurableSet_Icc fun x hx ↦ ?_
    simp only [g, Set.piecewise_eq_of_mem _ _ _ hx]
    rw [← ENNReal.ofReal_pow (hf₀ x hx), ← ENNReal.ofReal_mul (sq_nonneg _), mul_comm]
  · exact ((hf.pow 2).const_mul π).integrableOn_compact isCompact_Icc
  · exact (ae_restrict_mem measurableSet_Icc).mono fun x _ ↦ by positivity

/-- **Volume of a cone** of radius `R` and height `H`: one third of the cylinder with the same
base and height. -/
theorem volume_cone {R H : ℝ} (hR : 0 ≤ R) (hH : 0 < H) :
    volume {p : ℝ × EuclideanSpace ℝ (Fin 2) | p.1 ∈ Icc 0 H ∧ ‖p.2‖ ≤ R * p.1 / H} =
      ENNReal.ofReal (π * R ^ 2 * H / 3) := by
  refine (volume_solidOfRevolution (f := fun x ↦ R * x / H) hH.le (by fun_prop)
    fun x hx ↦ by have := hx.1; positivity).trans ?_
  congr 1
  have : (fun x : ℝ ↦ (R * x / H) ^ 2) = fun x ↦ (R / H) ^ 2 * x ^ 2 := by
    ext x
    ring
  rw [this, intervalIntegral.integral_const_mul, integral_pow]
  field_simp
  ring

end EuclideanSpace
