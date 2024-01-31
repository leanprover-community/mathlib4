/-
Copyright (c) 2022 Rishikesh Vaishnav. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rishikesh Vaishnav
-/
import Mathlib.MeasureTheory.Measure.Typeclasses

#align_import probability.conditional_probability from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

/-!
# Conditional Probability

This file defines conditional probability and includes basic results relating to it.

Given some measure `μ` defined on a measure space on some type `Ω` and some `s : Set Ω`,
we define the measure of `μ` conditioned on `s` as the restricted measure scaled by
the inverse of the measure of `s`: `cond μ s = (μ s)⁻¹ • μ.restrict s`. The scaling
ensures that this is a probability measure (when `μ` is a finite measure).

From this definition, we derive the "axiomatic" definition of conditional probability
based on application: for any `s t : Set Ω`, we have `μ[t|s] = (μ s)⁻¹ * μ (s ∩ t)`.

## Main Statements

* `cond_cond_eq_cond_inter`: conditioning on one set and then another is equivalent
  to conditioning on their intersection.
* `cond_eq_inv_mul_cond_mul`: Bayes' Theorem, `μ[t|s] = (μ s)⁻¹ * μ[s|t] * (μ t)`.

## Notations

This file uses the notation `μ[|s]` the measure of `μ` conditioned on `s`,
and `μ[t|s]` for the probability of `t` given `s` under `μ` (equivalent to the
application `μ[|s] t`).

These notations are contained in the locale `ProbabilityTheory`.

## Implementation notes

Because we have the alternative measure restriction application principles
`Measure.restrict_apply` and `Measure.restrict_apply'`, which require
measurability of the restricted and restricting sets, respectively,
many of the theorems here will have corresponding alternatives as well.
For the sake of brevity, we've chosen to only go with `Measure.restrict_apply'`
for now, but the alternative theorems can be added if needed.

Use of `@[simp]` generally follows the rule of removing conditions on a measure
when possible.

Hypotheses that are used to "define" a conditional distribution by requiring that
the conditioning set has non-zero measure should be named using the abbreviation
"c" (which stands for "conditionable") rather than "nz". For example `(hci : μ (s ∩ t) ≠ 0)`
(rather than `hnzi`) should be used for a hypothesis ensuring that `μ[|s ∩ t]` is defined.

## Tags
conditional, conditioned, bayes
-/


noncomputable section

open ENNReal MeasureTheory MeasurableSpace

variable {Ω : Type*} {m : MeasurableSpace Ω} (μ : Measure Ω) {s t : Set Ω}

namespace ProbabilityTheory

section Definitions

/-- The conditional probability measure of measure `μ` on set `s` is `μ` restricted to `s`
and scaled by the inverse of `μ s` (to make it a probability measure):
`(μ s)⁻¹ • μ.restrict s`. -/
def cond (s : Set Ω) : Measure Ω :=
  (μ s)⁻¹ • μ.restrict s
#align probability_theory.cond ProbabilityTheory.cond

end Definitions

@[inherit_doc] scoped notation μ "[" s "|" t "]" => ProbabilityTheory.cond μ t s
@[inherit_doc] scoped notation:60 μ "[|" t "]" => ProbabilityTheory.cond μ t

/-- The conditional probability measure of any finite measure on any set of positive measure
is a probability measure. -/
theorem cond_isProbabilityMeasure [IsFiniteMeasure μ] (hcs : μ s ≠ 0) :
    IsProbabilityMeasure (μ[|s]) :=
  ⟨by
    rw [cond, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    exact ENNReal.inv_mul_cancel hcs (measure_ne_top _ s)⟩
#align probability_theory.cond_is_probability_measure ProbabilityTheory.cond_isProbabilityMeasure

section Bayes

@[simp]
theorem cond_empty : μ[|∅] = 0 := by simp [cond]
#align probability_theory.cond_empty ProbabilityTheory.cond_empty

@[simp]
theorem cond_univ [IsProbabilityMeasure μ] : μ[|Set.univ] = μ := by
  simp [cond, measure_univ, Measure.restrict_univ]
#align probability_theory.cond_univ ProbabilityTheory.cond_univ

/-- The axiomatic definition of conditional probability derived from a measure-theoretic one. -/
theorem cond_apply (hms : MeasurableSet s) (t : Set Ω) : μ[t|s] = (μ s)⁻¹ * μ (s ∩ t) := by
  rw [cond, Measure.smul_apply, Measure.restrict_apply' hms, Set.inter_comm, smul_eq_mul]
#align probability_theory.cond_apply ProbabilityTheory.cond_apply

theorem cond_inter_self (hms : MeasurableSet s) (t : Set Ω) : μ[s ∩ t|s] = μ[t|s] := by
  rw [cond_apply _ hms, ← Set.inter_assoc, Set.inter_self, ← cond_apply _ hms]
#align probability_theory.cond_inter_self ProbabilityTheory.cond_inter_self

theorem inter_pos_of_cond_ne_zero (hms : MeasurableSet s) (hcst : μ[t|s] ≠ 0) : 0 < μ (s ∩ t) := by
  refine' pos_iff_ne_zero.mpr (right_ne_zero_of_mul _)
  · exact (μ s)⁻¹
  convert hcst
  simp [hms, Set.inter_comm, cond]
#align probability_theory.inter_pos_of_cond_ne_zero ProbabilityTheory.inter_pos_of_cond_ne_zero

theorem cond_pos_of_inter_ne_zero [IsFiniteMeasure μ]
    (hms : MeasurableSet s) (hci : μ (s ∩ t) ≠ 0) : 0 < (μ[|s]) t := by
  rw [cond_apply _ hms]
  refine' ENNReal.mul_pos _ hci
  exact ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)
#align probability_theory.cond_pos_of_inter_ne_zero ProbabilityTheory.cond_pos_of_inter_ne_zero

theorem cond_cond_eq_cond_inter' (hms : MeasurableSet s) (hmt : MeasurableSet t) (hcs : μ s ≠ ∞)
    (hci : μ (s ∩ t) ≠ 0) : μ[|s][|t] = μ[|s ∩ t] := by
  have hcs' : μ s ≠ 0 :=
    (μ.toOuterMeasure.pos_of_subset_ne_zero (Set.inter_subset_left _ _) hci).ne'
  ext u
  simp [*, hms.inter hmt, cond_apply, ← mul_assoc, ← Set.inter_assoc, ENNReal.mul_inv, mul_comm, ←
    mul_assoc, ENNReal.mul_inv_cancel]
#align probability_theory.cond_cond_eq_cond_inter' ProbabilityTheory.cond_cond_eq_cond_inter'

/-- Conditioning first on `s` and then on `t` results in the same measure as conditioning
on `s ∩ t`. -/
theorem cond_cond_eq_cond_inter [IsFiniteMeasure μ] (hms : MeasurableSet s) (hmt : MeasurableSet t)
    (hci : μ (s ∩ t) ≠ 0) : μ[|s][|t] = μ[|s ∩ t] :=
  cond_cond_eq_cond_inter' μ hms hmt (measure_ne_top μ s) hci
#align probability_theory.cond_cond_eq_cond_inter ProbabilityTheory.cond_cond_eq_cond_inter

theorem cond_mul_eq_inter' (hms : MeasurableSet s) (hcs : μ s ≠ 0) (hcs' : μ s ≠ ∞) (t : Set Ω) :
    μ[t|s] * μ s = μ (s ∩ t) := by
  rw [cond_apply μ hms t, mul_comm, ← mul_assoc, ENNReal.mul_inv_cancel hcs hcs', one_mul]
#align probability_theory.cond_mul_eq_inter' ProbabilityTheory.cond_mul_eq_inter'

theorem cond_mul_eq_inter [IsFiniteMeasure μ] (hms : MeasurableSet s) (hcs : μ s ≠ 0) (t : Set Ω) :
    μ[t|s] * μ s = μ (s ∩ t) :=
  cond_mul_eq_inter' μ hms hcs (measure_ne_top _ s) t
#align probability_theory.cond_mul_eq_inter ProbabilityTheory.cond_mul_eq_inter

/-- A version of the law of total probability. -/
theorem cond_add_cond_compl_eq [IsFiniteMeasure μ] (hms : MeasurableSet s) (hcs : μ s ≠ 0)
    (hcs' : μ sᶜ ≠ 0) : μ[t|s] * μ s + μ[t|sᶜ] * μ sᶜ = μ t := by
  rw [cond_mul_eq_inter μ hms hcs, cond_mul_eq_inter μ hms.compl hcs', Set.inter_comm _ t,
    Set.inter_comm _ t]
  exact measure_inter_add_diff t hms
#align probability_theory.cond_add_cond_compl_eq ProbabilityTheory.cond_add_cond_compl_eq

/-- **Bayes' Theorem** -/
theorem cond_eq_inv_mul_cond_mul [IsFiniteMeasure μ]
    (hms : MeasurableSet s) (hmt : MeasurableSet t) : μ[t|s] = (μ s)⁻¹ * μ[s|t] * μ t := by
  by_cases ht : μ t = 0
  · simp [cond, ht, Measure.restrict_apply hmt, Or.inr (measure_inter_null_of_null_left s ht)]
  · rw [mul_assoc, cond_mul_eq_inter μ hmt ht s, Set.inter_comm, cond_apply _ hms]
#align probability_theory.cond_eq_inv_mul_cond_mul ProbabilityTheory.cond_eq_inv_mul_cond_mul

end Bayes

end ProbabilityTheory
