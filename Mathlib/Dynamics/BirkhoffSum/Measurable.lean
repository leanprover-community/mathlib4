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
the corresponding average.  These are the step-one lemmas for measurability-sensitive ergodic
arguments.

The statements are codomain-general: `M` is any additive commutative monoid with a
measurable space structure whose addition is jointly measurable (in particular `ℝ`, `ℂ`,
or any second-countable topological vector space with its Borel σ-algebra), and the averaging
scalars live in any `DivisionSemiring` acting measurably on `M`.
-/

@[expose] public section

open Finset

variable {α : Type*} [MeasurableSpace α]
  {M : Type*} [MeasurableSpace M] [AddCommMonoid M] [MeasurableAdd₂ M]
  {R : Type*} [DivisionSemiring R] [Module R M] [MeasurableConstSMul R M]

/-- The Birkhoff sum of a measurable observable along measurable dynamics
is measurable. -/
theorem measurable_birkhoffSum {f : α → α} (hf : Measurable f)
    {g : α → M} (hg : Measurable g) (n : ℕ) :
    Measurable (birkhoffSum f g n) := by
  unfold birkhoffSum
  exact Finset.measurable_sum (range n) fun k _ => hg.comp (hf.iterate k)

/-- The Birkhoff average (time average) of a measurable observable along
measurable dynamics is measurable. -/
theorem measurable_birkhoffAverage {f : α → α} (hf : Measurable f)
    {g : α → M} (hg : Measurable g) (n : ℕ) :
    Measurable (birkhoffAverage R f g n) :=
  (measurable_birkhoffSum hf hg n).const_smul ((n : R)⁻¹)
