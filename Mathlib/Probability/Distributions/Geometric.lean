/-
Copyright (c) 2024 Josha Dekker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josha Dekker
-/

import Mathlib.Probability.Notation

/-! # Geometric distributions over ℕ

Define the geometric measure over the natural numbers

## Main definitions
* `geometricPmfReal`: the function `p x ↦ (1-p) ^ x * p`
  for `x ∈ ℕ`, which is the probability density function of a geometric distribution with
  success probability `p ∈ (0,1]`.
* `geometricPmf`: `ℝ≥0∞`-valued pdf,
  `geometricPmf p = ENNReal.ofReal (geometricPmfReal p)`.
* `geometricMeasure`: a geometric measure on `ℕ`, parametrized by its success probability `p`.
-/

open scoped ENNReal NNReal

open MeasureTheory Real Set Filter Topology

namespace ProbabilityTheory

section PoissonPmf

/-- The pmf of the geometric distribution depending on its success probability. -/
noncomputable
def geometricPmfReal (p : ℝ) (x : ℕ) : ℝ := (1-p) ^ x * p

lemma p_Ioc_to_one_le_Ico {p : ℝ} (hp : p ∈ Ioc 0 1) : 1-p ∈ Ico 0 1 := by
  have hl: 0 ≤ 1-p := by
    rw [sub_nonneg]
    exact hp.2
  have hu: 1-p < 1 := by
    simp only [sub_lt_self_iff]
    exact hp.1
  simp only [mem_Ico, sub_nonneg, sub_lt_self_iff]
  exact ⟨sub_nonneg.mp hl, (sub_lt_self_iff 1).mp hu⟩

lemma geometricPmfRealSum (p : ℝ) (hp : p ∈ Ioc 0 1) : HasSum (fun x ↦ geometricPmfReal p x) 1 := by
  unfold geometricPmfReal
  rw [mem_Ioc] at hp
  have hp_one := p_Ioc_to_one_le_Ico hp
  simp only [mem_Ico] at hp_one
  have := hasSum_geometric_of_lt_1 hp_one.1 hp_one.2
  apply (hasSum_mul_right_iff (hp.1.ne')).mpr at this
  simp only [sub_sub_cancel] at this
  rw [inv_mul_eq_div, div_self hp.1.ne'] at this
  exact this

/-- The geometric pmf is positive for all natural numbers -/
lemma geometricPmfReal_pos {p : ℝ} {x : ℕ} (hp : p ∈ Ioc 0 1) (hpn1 : p < 1) :
    0 < geometricPmfReal p x := by
  rw [geometricPmfReal]
  have : 0 < 1-p := sub_pos.mpr hpn1
  have : 0 < p := hp.1
  positivity

lemma geometricPmfReal_nonneg {p : ℝ} {x : ℕ}  (hp : p ∈ Ioc 0 1) : 0 ≤ geometricPmfReal p x := by
  rw [geometricPmfReal]
  have := (p_Ioc_to_one_le_Ico hp).1
  have : 0 ≤ p := hp.1.le
  positivity

/-- Geometric distribution with success probability `p`. -/
noncomputable
def geometricPmf {p : ℝ} (hp : p ∈ Ioc 0 1) : PMF ℕ := by
  refine ⟨fun x ↦ ENNReal.ofReal (geometricPmfReal p x), ?_⟩
  apply ENNReal.hasSum_coe.mpr
  rw [← toNNReal_one]
  exact (geometricPmfRealSum p hp).toNNReal (fun n ↦ geometricPmfReal_nonneg hp)

/-- The geometric pmf is measurable. -/
@[measurability]
lemma measurable_geometricPmfReal {p : ℝ} (hp : p ∈ Ioc 0 1) : Measurable (geometricPmfReal p) := by
  measurability

@[measurability]
lemma stronglyMeasurable_geometricPmfReal {p : ℝ} (hp : p ∈ Ioc 0 1) :
    StronglyMeasurable (geometricPmfReal p) :=
  stronglyMeasurable_iff_measurable.mpr (measurable_geometricPmfReal hp)

/-- Measure defined by the geometric distribution -/
noncomputable
def geometricMeasure {p : ℝ} (hp : p ∈ Ioc 0 1) : Measure ℕ := (geometricPmf hp).toMeasure

lemma isProbabilityMeasureGeometric {p : ℝ} (hp : p ∈ Ioc 0 1) :
    IsProbabilityMeasure (geometricMeasure hp) :=
  exact PMF.toMeasure.isProbabilityMeasure (geometricPmf hp )
