/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module geometry.manifold.metrizable
! leanprover-community/mathlib commit d1bd9c5df2867c1cb463bc6364446d57bdd9f7f1
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Geometry.Manifold.SmoothManifoldWithCorners
import Mathlib.Topology.Paracompact
import Mathlib.Topology.MetricSpace.Metrizable

/-!
# Metrizability of a σ-compact manifold

In this file we show that a σ-compact Hausdorff topological manifold over a finite dimensional real
vector space is metrizable.
-/


open TopologicalSpace

/-- A σ-compact Hausdorff topological manifold over a finite dimensional real vector space is
metrizable. -/
theorem ManifoldWithCorners.metrizableSpace {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {H : Type _} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    (M : Type _) [TopologicalSpace M] [ChartedSpace H M] [SigmaCompactSpace M] [T2Space M] :
    MetrizableSpace M := by
  haveI := I.locally_compact; haveI := ChartedSpace.locallyCompact H M
  haveI : NormalSpace M := normal_of_paracompact_t2
  haveI := I.secondCountableTopology
  haveI := ChartedSpace.secondCountable_of_sigma_compact H M
  exact metrizableSpace_of_t3_second_countable M
#align manifold_with_corners.metrizable_space ManifoldWithCorners.metrizableSpace
