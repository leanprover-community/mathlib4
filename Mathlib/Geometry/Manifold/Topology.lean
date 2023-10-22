/-
Copyright (c) 2023 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
import Mathlib.Geometry.Manifold.SmoothManifoldWithCorners

/-!
# Topological property of topological or smooth manifolds
In this file, we prove a few basic topological properties of manifolds.
Let $M$ be a topological manifold (not necessarily C^n or smooth).
* `locallyCompact_of_finiteDimensional_of_boundaryless`: If `M` is finite-dimensional, boundaryless
  and the underlying field `𝕜` is locally compact (such as ℝ, ℂ or the p-adic numbers),
  `M` is locally compact.

**TODO:**
* adapt the argument to include manifolds with boundary; this probably requires a
stronger definition of boundary to show local compactness of the half-spaces
-/

open Set Topology

variable
  {E : Type*} {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners 𝕜 E H) {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  -- Let M be a topological manifold over the field 𝕜.
  [HasGroupoid M (contDiffGroupoid 0 I)]

/-- Auxiliary lemma for local compactness of `M`. -/
lemma localCompactness_aux [LocallyCompactSpace 𝕜] [FiniteDimensional 𝕜 E]
    (hI : ModelWithCorners.Boundaryless I) {x : M} {n : Set M} (hn : n ∈ 𝓝 x) :
    ∃ s : Set M, s∈ 𝓝 x ∧ s ⊆ n ∧ IsCompact s  := by
  -- Assume `n` is contained in some chart at x. (Choose the distinguished chart from our atlas.)
  let chart := chartAt H x
  let echart := extChartAt I x
  have hn : n ∩ echart.source ∈ 𝓝 x := Filter.inter_mem hn
    (chart.extend_source_mem_nhds _ (mem_chart_source H x))

  -- Apply the chart to obtain a neighbourhood `n'` of $echart x ∈ E$.
  let x' := echart x
  let n' := echart '' (n ∩ echart.source)
  have hn' : n' ∈ 𝓝 x' := by
    let r := chart.map_extend_nhds I (mem_chart_source H x)
    rw [I.range_eq_univ, nhdsWithin_univ, ← extChartAt] at r
    exact r ▸ Filter.image_mem_map hn
  -- Since 𝕜 is locally compact, so is E. In particular, x' has a compact neighbourhood s' ⊆ n'.
  have : ProperSpace E := FiniteDimensional.proper 𝕜 E
  have : LocallyCompactSpace E := by infer_instance
  rcases this.local_compact_nhds x' n' hn' with ⟨s', hs', hsn', hscompact⟩
  -- Transport back: s := echart ⁻¹ (s') is a compact neighbourhood of x.
  let s := echart.symm '' s'
  have hstarget : s' ⊆ echart.target := calc s'
    _ ⊆ n' := hsn'
    _ ⊆ echart '' (echart.source) := image_subset _ (inter_subset_right _ _)
    _ ⊆ echart.target := LocalEquiv.map_source'' echart
  refine ⟨s, ?_, ?_, ?_⟩
  · -- FIXME: (how to) avoid the additional rewrites?
    let r := chart.extend_image_mem_nhds_symm I hs' hstarget
    have : LocalHomeomorph.extend chart I = echart := rfl
    rw [this, ← image_eta, (extChartAt_to_inv I x)] at r
    apply r
  · calc s
      _ ⊆ echart.symm '' n' := image_subset echart.symm hsn'
      _ = (echart.symm ∘ echart) '' (n ∩ echart.source) := by rw [image_comp]
      _ = n ∩ echart.source := by
        rw [extChartAt_source]
        apply chart.extend_left_inv' _ (inter_subset_right _ _)
      _ ⊆ n := inter_subset_left _ _
  · apply hscompact.image_of_continuousOn ((chart.continuousOn_extend_symm I).mono hstarget)

/-- A finite-dimensional manifold without boundary modelled on a locally compact field
  (such as ℝ, ℂ or the p-adic numbers) is locally compact. -/
-- FIXME: make this an instance!
-- TODO: also allow manifolds with boundary.
lemma Manifold.locallyCompact_of_finiteDimensional_of_boundaryless
    [LocallyCompactSpace 𝕜] [FiniteDimensional 𝕜 E] (hI : ModelWithCorners.Boundaryless I) :
    LocallyCompactSpace M := by
  exact { local_compact_nhds := fun x n hn ↦ localCompactness_aux I hI hn }
