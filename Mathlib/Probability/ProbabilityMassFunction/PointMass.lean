/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Devon Tuma
-/
module

public import Mathlib.Probability.ProbabilityMassFunction.Basic

/-!
# Probability mass functions (TODO redocument)

This file is about probability mass functions or discrete probability measures:
a function `α → ℝ≥0∞` such that the values have (infinite) sum `1`.

Construction of monadic `pure` and `bind` is found in
`Mathlib/Probability/ProbabilityMassFunction/Monad.lean`, other constructions of `PMF`s are found in
`Mathlib/Probability/ProbabilityMassFunction/Constructions.lean`.

Given `p : PMF α`, `PMF.toOuterMeasure` constructs an `OuterMeasure` on `α`,
by assigning each set the sum of the probabilities of each of its elements.
Under this outer measure, every set is Carathéodory-measurable,
so we can further extend this to a `Measure` on `α`, see `PMF.toMeasure`.
`PMF.toMeasure.isProbabilityMeasure` shows this associated measure is a probability measure.
Conversely, given a probability measure `μ` on a measurable space `α` with all singleton sets
measurable, `μ.toPMF` constructs a `PMF` on `α`, setting the probability mass of a point `x`
to be the measure of the singleton set `{x}`.

## Tags

probability mass function, discrete probability measure
-/

@[expose] public section


noncomputable section

variable {α : Type*}

open NNReal ENNReal MeasureTheory






namespace PMF

def pointMass (p : PMF α) (a : α) : NNReal := (p a).toNNReal

lemma apply_eq_pointMass_coe (p : PMF α) (a : α) : p a = (p.pointMass a : ENNReal) := by
  simp only [pointMass]
  lift p a to NNReal using apply_ne_top p a with x
  simp

protected theorem pointMass_ext {p q : PMF α} (h : ∀ x, p.pointMass x = q.pointMass x) : p = q := by
  ext x
  simp [apply_eq_pointMass_coe, h]

lemma eq_iff_pointMass {p q : PMF α} : p = q ↔ ∀ x, p.pointMass x = q.pointMass x := by
  constructor
  · intro rfl
    simp
  · exact PMF.pointMass_ext

theorem hasSum_pointMass_one (p : PMF α) : HasSum p.pointMass 1 := by
  sorry

@[simp]
theorem tsum_pointMass (p : PMF α) : ∑' a, p.pointMass a = 1 := by
  sorry

@[simp]
theorem pointMass_ne_zero (p : PMF α) : p.pointMass ≠ 0 := fun hp => by
  sorry

theorem mem_support_iff_pointMass (p : PMF α) (a : α) : a ∈ p.support ↔ p.pointMass a ≠ 0 := by
  sorry

theorem pointMass_eq_zero_iff (p : PMF α) (a : α) : p.pointMass a = 0 ↔ a ∉ p.support := by
  sorry

theorem pointMass_pos_iff (p : PMF α) (a : α) : 0 < p.pointMass a ↔ a ∈ p.support :=
  sorry

theorem pointMass_eq_one_iff (p : PMF α) (a : α) : p.pointMass a = 1 ↔ p.support = {a} := by
  sorry

theorem pointMass_le_one (p : PMF α) (a : α) : p.pointMass a ≤ 1 := by
  sorry

end PMF
