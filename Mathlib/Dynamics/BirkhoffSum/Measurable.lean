/-
Copyright (c) 2026 Radu Irbe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Radu Irbe
-/
module

public import Mathlib.Dynamics.BirkhoffSum.Average
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

/-!
# Measurability of Birkhoff sums and averages

The Birkhoff sum of a measurable observable along measurable dynamics is measurable, and so is
the corresponding average. These are the step-one lemmas for measurability-sensitive ergodic
arguments.
-/

@[expose] public section

open Finset

variable {α : Type*} [MeasurableSpace α]

/-- The Birkhoff sum of a measurable observable along measurable dynamics
is measurable. -/
theorem measurable_birkhoffSum {f : α → α} (hf : Measurable f)
    {g : α → ℝ} (hg : Measurable g) (n : ℕ) :
    Measurable (birkhoffSum f g n) := by
  unfold birkhoffSum
  refine Finset.measurable_sum (range n) ?_
  intro k _
  exact hg.comp (hf.iterate k)

/-- The Birkhoff average (time average) of a measurable observable along
measurable dynamics is measurable. -/
theorem measurable_birkhoffAverage {f : α → α} (hf : Measurable f)
    {g : α → ℝ} (hg : Measurable g) (n : ℕ) :
    Measurable (birkhoffAverage ℝ f g n) := by
  unfold birkhoffAverage
  exact (measurable_birkhoffSum hf hg n).const_smul ((n : ℝ)⁻¹)
