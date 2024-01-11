/-
Copyright (c) 2024 Josha Dekker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josha Dekker
-/

import Mathlib.Probability.Notation

/-! # Geometric distributions over ℕ

Define the geometric measure over the natural numbers

## Main definitions
* `geometricPmfReal`: the function `p n ↦ (1-p) ^ n * p`
  for `n ∈ ℕ`, which is the probability density function of a geometric distribution with
  success probability `p ∈ (0,1]`.
* `geometricPmf`: `ℝ≥0∞`-valued pdf,
  `geometricPmf p = ENNReal.ofReal (geometricPmfReal p)`.
* `geometricMeasure`: a geometric measure on `ℕ`, parametrized by its success probability `p`.
-/

open scoped ENNReal NNReal

open MeasureTheory Real Set Filter Topology

namespace ProbabilityTheory

section GeometricPmf

/-- The pmf of the geometric distribution depending on its success probability. -/
noncomputable
def geometricPmfReal (p : ℝ) (n : ℕ) : ℝ := (1-p) ^ n * p

lemma geometricPmfRealSum {p : ℝ} (hp_pos : 0 < p) (hp_le_one : p <= 1) :
    HasSum (fun n ↦ geometricPmfReal p n) 1 := by
  unfold geometricPmfReal
  have := hasSum_geometric_of_lt_1 (sub_nonneg.mpr hp_le_one) (sub_lt_self 1 hp_pos)
  apply (hasSum_mul_right_iff (hp_pos.ne')).mpr at this
  simp only [sub_sub_cancel] at this
  rw [inv_mul_eq_div, div_self hp_pos.ne'] at this
  exact this

/-- The geometric pmf is positive for all natural numbers -/
lemma geometricPmfReal_pos {p : ℝ} {n : ℕ} (hp_pos : 0 < p) (hp_lt_one : p < 1) :
    0 < geometricPmfReal p n := by
  rw [geometricPmfReal]
  have : 0 < 1-p := sub_pos.mpr hp_lt_one
  positivity

lemma geometricPmfReal_nonneg {p : ℝ} {n : ℕ}  (hp_pos : 0 < p) (hp_le_one : p <= 1) :
    0 ≤ geometricPmfReal p n := by
  rw [geometricPmfReal]
  have : 0 ≤ 1-p := sub_nonneg.mpr hp_le_one
  positivity

/-- Geometric distribution with success probability `p`. -/
noncomputable
def geometricPmf {p : ℝ} (hp_pos : 0 < p) (hp_le_one : p <= 1) : PMF ℕ := by
  refine ⟨fun n ↦ ENNReal.ofReal (geometricPmfReal p n), ?_⟩
  apply ENNReal.hasSum_coe.mpr
  rw [← toNNReal_one]
  exact (geometricPmfRealSum hp_pos hp_le_one).toNNReal
    (fun n ↦ geometricPmfReal_nonneg hp_pos hp_le_one)

/-- The geometric pmf is measurable. -/
@[measurability]
lemma measurable_geometricPmfReal {p : ℝ} : Measurable (geometricPmfReal p) := by
  measurability

@[measurability]
lemma stronglyMeasurable_geometricPmfReal {p : ℝ} :
    StronglyMeasurable (geometricPmfReal p) :=
  stronglyMeasurable_iff_measurable.mpr measurable_geometricPmfReal

end GeometricPmf

/-- Measure defined by the geometric distribution -/
noncomputable
def geometricMeasure {p : ℝ} (hp_pos : 0 < p) (hp_le_one : p <= 1) : Measure ℕ :=
    (geometricPmf hp_pos hp_le_one).toMeasure

lemma isProbabilityMeasureGeometric {p : ℝ} (hp_pos : 0 < p) (hp_le_one : p <= 1) :
    IsProbabilityMeasure (geometricMeasure hp_pos hp_le_one) :=
  PMF.toMeasure.isProbabilityMeasure (geometricPmf hp_pos hp_le_one)

end ProbabilityTheory
