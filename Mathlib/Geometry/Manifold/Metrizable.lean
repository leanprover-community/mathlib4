/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.Topology.Compactness.Paracompact
public import Mathlib.Topology.Metrizable.Urysohn

@[expose] public section

/-!
# Metrizability of a σ-compact manifold

In this file we show that a σ-compact Hausdorff topological manifold over a finite-dimensional real
vector space is metrizable.
-/


open TopologicalSpace

/-- A σ-compact Hausdorff topological manifold over a finite-dimensional real vector space is
metrizable. -/
theorem Manifold.metrizableSpace {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [SigmaCompactSpace M] [T2Space M] :
    MetrizableSpace M := by
  haveI := I.locallyCompactSpace; haveI := ChartedSpace.locallyCompactSpace H M
  haveI := I.secondCountableTopology
  haveI := ChartedSpace.secondCountable_of_sigmaCompact H M
  exact metrizableSpace_of_t3_secondCountable M
