/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Geometry.Manifold.SmoothManifoldWithCorners
import Mathlib.Topology.Paracompact
import Mathlib.Topology.MetricSpace.Metrizable

#align_import geometry.manifold.metrizable from "leanprover-community/mathlib"@"d1bd9c5df2867c1cb463bc6364446d57bdd9f7f1"

/-!
# Metrizability of a σ-compact manifold

In this file we show that a σ-compact Hausdorff topological manifold over a finite dimensional real
vector space is metrizable.
-/


open TopologicalSpace

/-- A σ-compact Hausdorff topological manifold over a finite dimensional real vector space is
metrizable. -/
theorem ManifoldWithCorners.metrizableSpace {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [SigmaCompactSpace M] [T2Space M] :
    MetrizableSpace M := by
  haveI := I.locallyCompactSpace; haveI := ChartedSpace.locallyCompactSpace H M
  -- ⊢ MetrizableSpace M
                                  -- ⊢ MetrizableSpace M
  haveI : NormalSpace M := normal_of_paracompact_t2
  -- ⊢ MetrizableSpace M
  haveI := I.secondCountableTopology
  -- ⊢ MetrizableSpace M
  haveI := ChartedSpace.secondCountable_of_sigma_compact H M
  -- ⊢ MetrizableSpace M
  exact metrizableSpace_of_t3_second_countable M
  -- 🎉 no goals
#align manifold_with_corners.metrizable_space ManifoldWithCorners.metrizableSpace
