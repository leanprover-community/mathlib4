/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

import Mathlib.Analysis.Normed.Lp.SmoothApprox

/-!
# Density of Schwartz functions in `L^p`

This file proves that the range of the inclusion `SchwartzMap.toLpCLM` of the Schwartz space
into `L^p` is dense.

This is split off from `Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean` because the
proof relies on the approximation of `L^p` functions by smooth compactly supported functions,
which sits on top of a large part of the manifold library; keeping it out of the main file
shortens Mathlib's critical build path.

## Main statements

* `SchwartzMap.denseRange_toLpCLM`: Schwartz functions are dense in `L^p`.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [MeasurableSpace E] [OpensMeasurableSpace E]

namespace SchwartzMap

/-- Schwartz functions are dense in `Lp`. -/
theorem denseRange_toLpCLM [FiniteDimensional ℝ E] [BorelSpace E] {p : ℝ≥0∞} (hp : p ≠ ⊤)
    [hp' : Fact (1 ≤ p)] {μ : Measure E} [hμ : μ.HasTemperateGrowth] [IsFiniteMeasureOnCompacts μ] :
    DenseRange (SchwartzMap.toLpCLM ℝ F p μ) := by
  intro f
  refine (mem_closure_iff_nhds_basis Metric.nhds_basis_closedBall).2 fun ε hε ↦ ?_
  obtain ⟨g, hg₁, hg₂, hg₃⟩ := MemLp.exist_eLpNorm_sub_le hp hp'.out (Lp.memLp f) hε
  use (hg₁.toSchwartzMap hg₂).toLp p μ
  have : (f : E → F) - ((hg₁.toSchwartzMap hg₂).toLp p μ : E → F) =ᵐ[μ] (f : E → F) - g := by
    filter_upwards [(hg₁.toSchwartzMap hg₂).coeFn_toLp p μ]
    simp
  simp only [Set.mem_range, toLpCLM_apply, exists_apply_eq_apply, Metric.mem_closedBall', true_and,
    Lp.dist_def, eLpNorm_congr_ae this]
  grw [hg₃, ENNReal.toReal_ofReal hε.le]
  simp

end SchwartzMap
