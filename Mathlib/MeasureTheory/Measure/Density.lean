/-
Copyright (c) 2026 Felix Pernegger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Felix Pernegger
-/
module

public import Mathlib.MeasureTheory.Measure.OpenPos

import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.Order.Filter.ENNReal
import Mathlib.Tactic.Linarith.NNRealPreprocessor

/-!
# Density of sets in metric space with a measure

We define a general notion of density of a set in a metric space with a measure.
This unifies the definitions of density used in packing problems
and natural density in combinatorics.

## Main definitions

* `MeasureTheory.lowerDensityAt μ s`, the lower density of a set w.r.t. measure `s`.
* `MeasureTheory.upperDensityAt μ s`, the upper density of a set w.r.t. measure `s`.

## TODO

* Generalize `ProperSpace` to use `PseudoEMetricSpace` and fix the results in section `ProperSpace`.
* Give explicit descriptions for the density for finite measures.
* Show that in well-behaved spaces, the basepoint is irrelevant
* Connect the definition with natural density from combinatorics

-/

@[expose] public section

universe u

open ENNReal Filter Set NNReal

namespace MeasureTheory

variable {X : Type u} [MeasurableSpace X] [PseudoEMetricSpace X]

/-- Helper function to define lower and upper density of a set. -/
noncomputable def densityQuotientAt (μ : Measure X := by volume_tac) (s : Set X) (x : X) (r : ℝ≥0) :
    ℝ≥0∞ :=
  letI B := Metric.eball x r
  μ (s ∩ B) / μ (B)

/-- The lower density of a set in a pseudo extended metric space with a measure at a basepoint.

Note that for well behaved spaces, the choice of the basepoint does not matter. -/
noncomputable def lowerDensityAt (μ : Measure X := by volume_tac) (s : Set X) (x : X) : ℝ≥0∞ :=
  liminf (densityQuotientAt μ s x) atTop

/-- The upper density of a set in a pseudo extended metric space with a measure at a basepoint.

Note that for well behaved spaces, the choice of the basepoint does not matter. -/
noncomputable def upperDensityAt (μ : Measure X := by volume_tac) (s : Set X) (x : X) : ℝ≥0∞ :=
  limsup (densityQuotientAt μ s x) atTop

@[simp]
theorem densityQuotientAt_radius_zero (μ : Measure X := by volume_tac) (s : Set X) (x : X) :
    densityQuotientAt μ s x 0 = 0 := by
  simp [densityQuotientAt]

theorem lowerDensityAt_le_upperDensityAt (μ : Measure X := by volume_tac) (s : Set X) (x : X) :
    lowerDensityAt μ s x ≤ upperDensityAt μ s x :=
  liminf_le_limsup

theorem densityQuotientAt_le_one (μ : Measure X := by volume_tac) (s : Set X) (x : X) (r : ℝ≥0) :
    densityQuotientAt μ s x r ≤ 1 := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  · unfold densityQuotientAt
    apply ENNReal.div_le_of_le_mul'
    grw [mul_one, measure_mono inter_subset_right]

theorem upperDensityAt_le_one (μ : Measure X := by volume_tac) (s : Set X) (x : X) :
    upperDensityAt μ s x ≤ 1 := by
  unfold upperDensityAt
  apply le_trans Filter.limsup_le_iSup
  simp [densityQuotientAt_le_one]

theorem lowerDensityAt_le_one (μ : Measure X := by volume_tac) (s : Set X) (x : X) :
    lowerDensityAt μ s x ≤ 1 :=
  le_trans (lowerDensityAt_le_upperDensityAt μ s x) (upperDensityAt_le_one μ s x)

@[gcongr]
theorem densityQuotientAt_congr (μ : Measure X := by volume_tac) {s t : Set X} (x : X) (r : ℝ≥0)
    (st : s =ᵐ[μ] t) :
    densityQuotientAt μ s x r = densityQuotientAt μ t x r := by
  unfold densityQuotientAt
  rw [measure_congr <| ae_eq_set_inter st (EventuallyEqSet.rfl)]

@[gcongr]
theorem lowerDensityAt_congr (μ : Measure X := by volume_tac) {s t : Set X}
    (x : X) (st : s =ᵐ[μ] t) :
    lowerDensityAt μ s x = lowerDensityAt μ t x := by
  unfold lowerDensityAt
  congr 1 with r
  exact densityQuotientAt_congr μ x r st

@[gcongr]
theorem upperDensityAt_congr (μ : Measure X := by volume_tac) {s t : Set X}
    (x : X) (st : s =ᵐ[μ] t) :
    upperDensityAt μ s x = upperDensityAt μ t x := by
  unfold upperDensityAt
  congr 1 with r
  exact densityQuotientAt_congr μ x r st

section ProperSpace -- see TODO at the module header

variable {X : Type u} [MeasurableSpace X] [PseudoMetricSpace X]

theorem densityQuotientAt_univ [ProperSpace X] (μ : Measure X := by volume_tac) [μ.IsOpenPosMeasure]
    [IsFiniteMeasureOnCompacts μ] (x : X) {r : ℝ≥0} (hr : 0 < r) :
    densityQuotientAt μ univ x r = 1 := by
  rw [densityQuotientAt, inf_of_le_right (subset_univ _)]
  apply ENNReal.div_self (Metric.measure_eball_pos μ x (by norm_cast; grind)).ne.symm
  rw [Metric.eball_coe]
  exact measure_ball_ne_top

@[simp]
theorem lowerDensityAt_univ [ProperSpace X] (μ : Measure X := by volume_tac) [μ.IsOpenPosMeasure]
    [IsFiniteMeasureOnCompacts μ] (x : X) :
    lowerDensityAt μ univ x = 1 := by
  unfold lowerDensityAt
  apply Tendsto.liminf_eq <| tendsto_nhds_of_eventually_eq ?_
  exact eventually_atTop.mpr ⟨1, fun r hr ↦ densityQuotientAt_univ μ x (by linarith)⟩

@[simp]
theorem upperDensityAt_univ [ProperSpace X] (μ : Measure X := by volume_tac) [μ.IsOpenPosMeasure]
    [IsFiniteMeasureOnCompacts μ] (x : X) :
    upperDensityAt μ univ x = 1 := by
  apply le_antisymm
  · exact upperDensityAt_le_one μ univ x
  · grw [← lowerDensityAt_univ μ x, lowerDensityAt_le_upperDensityAt μ univ x]

end ProperSpace

theorem densityQuotientAt_of_measure_zero (μ : Measure X := by volume_tac) {s : Set X} (x : X)
    (hs : μ s = 0) :
    densityQuotientAt μ s x = 0 := by
  ext r
  simp [densityQuotientAt, measure_inter_null_of_null_left (Metric.eball x ↑r) hs]

theorem upperDensityAt_of_measure_zero (μ : Measure X := by volume_tac) {s : Set X} (x : X)
    (hs : μ s = 0) :
    upperDensityAt μ s x = 0 := by
  simp [upperDensityAt, limsup, limsSup, densityQuotientAt_of_measure_zero μ x (hs := hs)]

theorem lowerDensityAt_of_measure_zero (μ : Measure X := by volume_tac) {s : Set X} (x : X)
    (hs : μ s = 0) :
    lowerDensityAt μ s x = 0 :=
  le_antisymm (le_trans (lowerDensityAt_le_upperDensityAt μ s x)
    (upperDensityAt_of_measure_zero μ x hs).le) zero_le

@[simp]
lemma densityQuotientAt_empty (μ : Measure X := by volume_tac) (x : X) :
    densityQuotientAt μ ∅ x = 0 :=
  densityQuotientAt_of_measure_zero μ x measure_empty

@[simp]
lemma upperDensityAt_empty (μ : Measure X := by volume_tac) (x : X) :
    upperDensityAt μ ∅ x = 0 :=
  upperDensityAt_of_measure_zero μ x measure_empty

@[simp]
lemma lowerDensityAt_empty (μ : Measure X := by volume_tac) (x : X) :
    lowerDensityAt μ ∅ x = 0 :=
  lowerDensityAt_of_measure_zero μ x measure_empty

@[gcongr]
theorem densityQuotientAt.mono (μ : Measure X := by volume_tac) (x : X) (r : ℝ≥0) {s t : Set X}
    (st : s ⊆ t) : densityQuotientAt μ s x r ≤ densityQuotientAt μ t x r := by
  unfold densityQuotientAt
  gcongr

@[gcongr]
theorem lowerDensityAt.mono (μ : Measure X := by volume_tac) (x : X) {s t : Set X}
    (st : s ⊆ t) : lowerDensityAt μ s x ≤ lowerDensityAt μ t x := by
  unfold lowerDensityAt
  refine liminf_le_liminf ?_ ?_ ?_
  · filter_upwards with
    gcongr
  · exact BddBelow.isBoundedUnder_of_range (by simp)
  · exact IsBoundedUnder.isCoboundedUnder_ge isBounded_le_of_top

theorem densityQuotient_union [OpensMeasurableSpace X] (μ : Measure X := by volume_tac) (x : X)
    {s t : Set X} (r : ℝ≥0) (ht : NullMeasurableSet t μ) (st : Disjoint s t) :
    densityQuotientAt μ (s ∪ t) x r = densityQuotientAt μ s x r + densityQuotientAt μ t x r := by
  unfold densityQuotientAt
  rw [union_inter_distrib_right, measure_union₀ (ht.inter measurableSet_eball.nullMeasurableSet)
    (st.mono inter_subset_left inter_subset_left).aedisjoint, ENNReal.add_div]

theorem densityQuotientAt_union_le (μ : Measure X := by volume_tac) (x : X) (s t : Set X)
    (r : ℝ≥0) :
    densityQuotientAt μ (s ∪ t) x r ≤ densityQuotientAt μ s x r + densityQuotientAt μ t x r := by
  unfold densityQuotientAt
  grw [union_inter_distrib_right, ← ENNReal.add_div, measure_union_le]

/-- The lower density of a set is superadditive. -/
theorem lowerDensityAt_add_le_union [OpensMeasurableSpace X] (μ : Measure X := by volume_tac)
    (x : X) {s t : Set X} (ht : NullMeasurableSet t μ) (st : Disjoint s t) :
    lowerDensityAt μ s x + lowerDensityAt μ t x ≤ lowerDensityAt μ (s ∪ t) x := by
  unfold lowerDensityAt
  apply le_of_le_of_eq (ENNReal.le_liminf_add _ _)
  congr with r
  rw [densityQuotient_union μ x r ht st, Pi.add_apply]

/-- The upper density of a set is subadditive. -/
theorem upperDensityAt_union_le (μ : Measure X := by volume_tac) (x : X) (s t : Set X) :
    upperDensityAt μ (s ∪ t) x ≤ upperDensityAt μ s x + upperDensityAt μ t x := by
  unfold upperDensityAt
  refine le_trans (limsup_le_limsup ?_) (ENNReal.limsup_add_le _ _)
  filter_upwards with r
  exact densityQuotientAt_union_le μ x s t r

end MeasureTheory
