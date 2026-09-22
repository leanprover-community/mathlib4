/-
Copyright (c) 2026 Bjørn Solheim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Solheim
-/
module

public import Mathlib.Analysis.Convex.Topology
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# Compact convex hulls

The convex hull of a compact set in a finite-dimensional topological vector space over
a linearly ordered field with an order closed topology and compact closed intervals is compact.

## Main results

* `Set.convexHull_eq_range_sum_smul`: the convex hull of `K ⊆ E` is the range of weighted sums of
  `finrank 𝕜 E + 1` points of `K`, with nonnegative weights summing to one.
* `IsCompact.convexHull`: the convex hull of a compact set is compact.

## Implementation notes

Carathéodory's theorem says that every point in the convex hull of `K ⊆ E` is a convex
combination of at most `n + 1` points of `K`, where `n = finrank 𝕜 E`. This is used to express
the convex hull as the range of the weighted-sum map on
the product of the standard `n`-simplex and the set of `(n + 1)`-tuples of points of `K`.
When `E` is a topological vector space, the weighted-sum map is continuous.
When `K` itself and closed intervals in the scalar field are compact,
then the whole domain is compact. Hence, under these conditions, the range,
which is equal to the convex hull, is also compact.

The counterpart for finite sets in arbitrary dimension is `Set.Finite.isCompact_convexHull`.
-/

public section

open Set Convexity Module

variable {𝕜 E : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [FiniteDimensional 𝕜 E]

attribute [local instance] ConvexSpace.ofModule in
/-- In finite dimensions, the convex hull of `K ⊆ E` is the range of weighted sums of
`finrank 𝕜 E + 1` points of `K`, with nonnegative weights summing to one. -/
theorem Set.convexHull_eq_range_sum_smul (K : Set E) :
    convexHull 𝕜 K = range
      (fun p : StdSimplex 𝕜 (Fin (finrank 𝕜 E + 1)) ×
        (Fin (finrank 𝕜 E + 1) → K) ↦ ∑ i, p.1.weights i • (p.2 i : E)) := by
  refine Subset.antisymm (fun x hx ↦ ?_) (range_subset_iff.mpr fun ⟨w, z⟩ ↦ ?_)
  · obtain ⟨t, htK, hind, hxt⟩ : ∃ t : Finset E,
        (t : Set E) ⊆ K ∧ AffineIndependent 𝕜 ((↑) : t → E) ∧
          x ∈ convexHull 𝕜 (t : Set E) := by
      rw [convexHull_eq_union] at hx
      simpa only [mem_iUnion, exists_prop] using hx
    let e : ↥(t : Set E) ↪ Fin (finrank 𝕜 E + 1) := (Fintype.equivFin _).toEmbedding.trans <|
      Fin.castLEEmb <| hind.card_le_finrank_succ.trans (Nat.succ_le_succ (Submodule.finrank_le _))
    obtain ⟨w, hw⟩ := (convexHull_eq_range_iConvexComb (t : Set E)).subset hxt
    let z : ↥(t : Set E) → K := fun i ↦ ⟨i, htK i.2⟩
    -- get arbitrary padding element `k ∈ K`
    obtain ⟨k, hk⟩ : K.Nonempty := convexHull_nonempty_iff.mp ⟨x, hx⟩
    -- fill with `0` for weights (by `w.map e`) and `k` for points (by `Function.extend`)
    refine ⟨⟨w.map e, Function.extend e z fun _ ↦ ⟨k, hk⟩⟩, ?_⟩
    simpa only [← StdSimplex.affineMapMk_apply_eq_sum_of_fintype, StdSimplex.affineMapMk_apply,
      iConvexComb_map, e.injective.extend_apply] using hw
  · exact (convex_convexHull 𝕜 K).sum_mem (fun i _ ↦ w.weights_nonneg i) w.total_of_fintype
      fun i _ ↦ subset_convexHull 𝕜 K (z i).2

variable (𝕜) [TopologicalSpace 𝕜] [OrderClosedTopology 𝕜] [CompactIccSpace 𝕜] [IsTopologicalRing 𝕜]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]

attribute [local instance] ConvexSpace.ofModule in
/-- In finite dimensions, the convex hull of a compact set is compact.
See also `Set.Finite.isCompact_convexHull`. -/
theorem IsCompact.convexHull {K : Set E} (hK : IsCompact K) :
    IsCompact (convexHull 𝕜 K) := by
  rw [convexHull_eq_range_sum_smul K]
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  exact isCompact_range (by fun_prop)
