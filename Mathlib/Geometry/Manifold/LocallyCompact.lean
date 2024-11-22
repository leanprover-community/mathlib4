/-
Copyright (c) 2024 Winston Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin
-/
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Geometry.Manifold.SmoothManifoldWithCorners

/-!
# Locally compact manifolds are finite dimensional

-/

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) [I.Boundaryless]
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
  [Inhabited M] [LocallyCompactSpace M]

include I M in
lemma LocallyCompactSpace.of_locallyCompact_manifold :
    LocallyCompactSpace E := by
  have x : M := Inhabited.default
  obtain ⟨s, hs1, hs2, hs3⟩ :=
    local_compact_nhds x (extChartAt I x).source (extChartAt_source_mem_nhds x)
  have : IsCompact <| (extChartAt I x) '' s :=
    hs3.image_of_continuousOn <| ContinuousOn.mono (continuousOn_extChartAt x) hs2
  apply this.locallyCompactSpace_of_mem_nhds_of_addGroup (x := extChartAt I x x)
  exact extChartAt_image_nhd_mem_nhds_of_boundaryless hs1

include I M in
theorem FiniteDimensional.of_locallyCompact_manifold [CompleteSpace 𝕜] :
    FiniteDimensional 𝕜 E := by
  have := LocallyCompactSpace.of_locallyCompact_manifold I M
  exact FiniteDimensional.of_locallyCompactSpace 𝕜
