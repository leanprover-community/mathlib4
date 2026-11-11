/-
Copyright (c) 2023 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot, Justus Springer
-/
module

public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Measure.Lebesgue.Parallelepiped

/-!
# Covolume of lattices

## Main statements

* `Module.Basis.isAddFundamentalDomain_halfOpenParallelepiped`: the half-open parallelepiped
  spanned by a basis `b` of a real normed space is a fundamental domain of `span ℤ (range b)`.
-/

@[expose] public section

open MeasureTheory Set Submodule

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] (b : Module.Basis ι ℝ E)

theorem Module.Basis.isAddFundamentalDomain_halfOpenParallelepiped (μ : Measure E) :
    IsAddFundamentalDomain (span ℤ (range b)) (halfOpenParallelepiped ℝ b) μ :=
  .mk' (measurableSet_halfOpenParallelepiped b).nullMeasurableSet
    b.existsUnique_vadd_mem_halfOpenParallelepiped
