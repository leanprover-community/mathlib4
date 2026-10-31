/-
Copyright (c) 2026 Bjørn Solheim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Solheim
-/
module

public import Mathlib.Analysis.Convex.Exposed
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

import Mathlib.Analysis.Convex.Compact
import Mathlib.Analysis.Convex.Strict.Exposed
import Mathlib.Analysis.InnerProductSpace.Convex
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.LocallyConvex.Separation

/-!
# Straszewicz's theorem

Every extreme point of a closed convex set `K` in a finite-dimensional Hausdorff real
topological vector space belongs to the closure of the set of exposed points of `K`.
Straszewicz's original theorem, for compact convex sets, is the special case obtained through
`IsCompact.isClosed`.

## Main results

* `IsClosed.extremePoints_subset_closure_exposedPoints`: Straszewicz's theorem. Extreme points
  of a closed convex set are limits of exposed points.
* `IsClosed.closure_exposedPoints`: exposed and extreme points of a closed convex set have equal
  closure.

## Implementation notes

The proof of `IsClosed.extremePoints_subset_closure_exposedPoints` is carried out in
`EuclideanSpace ℝ (Fin (Module.finrank ℝ E))`, since `E` carries no norm, and transported back
along a continuous linear equivalence. There, for an extreme point `x` and `ε > 0`, a point of
`K ∩ closedBall x ε` farthest from a suitable center lies in `ball x ε` and is exposed in `K`.

## References

* [S. Straszewicz, *Über exponierte Punkte abgeschlossener Punktmengen* (§6)][straszewicz1935],
  for compact sets
* [R. T. Rockafellar, *Convex Analysis* (Theorem 18.6)][rockafellar1970], for closed sets
-/

open Set

open scoped RealInnerProductSpace

section Hilbert
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

open Metric in
/-- In a real Hilbert space, for a point `x` outside a closed, bounded, convex set `C` there is a
point `c` such that every point of `C` is strictly closer to `c` than `x` is. Equivalently, `x`
lies on the sphere of an open ball with center `c` that contains `C`. -/
theorem Convex.exists_forall_dist_lt_dist_of_notMem {C : Set E} {x : E} (hc : Convex ℝ C)
    (hCc : IsClosed C) (hCb : Bornology.IsBounded C) (hx : x ∉ C) :
    ∃ c, ∀ y ∈ C, dist y c < dist x c := by
  -- Separate `x` from `C` by the functional `l`, represent `l` by the vector `a`, and bound `C` by
  -- a ball of radius `r` around `x`. The center `c = x - t • a` works once `r ^ 2 < t * (l x - u)`.
  obtain ⟨l, u, hl, hlx⟩ := geometric_hahn_banach_closed_point hc hCc hx
  obtain ⟨a, ha⟩ : ∃ a : E, ∀ v, ⟪v, a⟫ = l v :=
    ⟨_, fun _ ↦ (real_inner_comm _ _).trans InnerProductSpace.toDual_symm_apply⟩
  obtain ⟨r, hr⟩ := hCb.subset_closedBall x
  obtain ⟨t, ht, hrt⟩ := exists_pos_lt_mul (sub_pos.mpr hlx) (r ^ 2)
  refine ⟨x - t • a, fun w hw ↦ lt_of_pow_lt_pow_left₀ 2 dist_nonneg ?_⟩
  have hwr : dist w x ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ dist_nonneg (mem_closedBall.mp (hr hw)) 2
  calc dist w (x - t • a) ^ 2
      = dist w x ^ 2 + 2 * (t * (l w - l x)) + dist x (x - t • a) ^ 2 := by
        rw [dist_self_sub_right, dist_eq_norm, dist_eq_norm, ← sub_add, norm_add_sq_real,
          real_inner_smul_right, ha, map_sub]
    _ < dist x (x - t • a) ^ 2 := by linarith [mul_lt_mul_of_pos_left (hl w hw) ht, sq_nonneg r]

end Hilbert

section InnerProduct
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

open Metric in
/-- In a finite-dimensional real inner product space, every extreme point of a closed convex set
is a limit of exposed points. -/
theorem extremePoints_subset_closure_exposedPoints_inner {K : Set E}
    (hK : IsClosed K) (hc : Convex ℝ K) : K.extremePoints ℝ ⊆ closure (K.exposedPoints ℝ) := by
  refine fun x hx ↦ (mem_closure_iff_nhds_basis nhds_basis_ball).mpr fun ε hε ↦ ?_
  -- `K \ {x}` is convex because `x` is extreme, so it contains the convex hull of the compact set
  -- `K ∩ sphere x ε`. Hence there is a point `c` such that every point of this hull is strictly
  -- closer to `c` than `x` is.
  have hsub : convexHull ℝ (K ∩ sphere x ε) ⊆ K \ {x} :=
    convexHull_min (fun _ hw ↦ ⟨hw.1, ne_of_mem_sphere hw.2 hε.ne'⟩)
      (hc.mem_extremePoints_iff_convex_sdiff.mp hx).2
  have hH : IsCompact (convexHull ℝ (K ∩ sphere x ε)) :=
    ((isCompact_sphere x ε).inter_left hK).convexHull ℝ
  obtain ⟨c, hcH⟩ := (convex_convexHull ℝ _).exists_forall_dist_lt_dist_of_notMem hH.isClosed
    hH.isBounded fun h ↦ (hsub h).2 (mem_singleton x)
  -- A point `y` of `K ∩ closedBall x ε` farthest from `c` is at least as far from `c` as `x`, so
  -- it is not on `sphere x ε`: it lies in `ball x ε`, where `closedBall x ε` is a neighborhood of
  -- `y`.
  have hxKB : x ∈ K ∩ closedBall x ε := ⟨hx.1, mem_closedBall_self hε.le⟩
  obtain ⟨y, hyKB, hymax⟩ := ((isCompact_closedBall x ε).inter_left hK).exists_isMaxOn ⟨x, hxKB⟩
    (f := (dist · c)) (by fun_prop)
  have hyB : y ∈ ball x ε := mem_ball.mpr <| (mem_closedBall.mp hyKB.2).lt_of_ne fun h ↦
    (hcH _ (subset_convexHull ℝ _ ⟨hyKB.1, mem_sphere.mpr h⟩)).not_ge (hymax hxKB)
  exact ⟨y, (hc.mem_exposedPoints_inter_iff (closedBall_mem_nhds_of_mem hyB)).mp
    (StrictConvexSpace.mem_exposedPoints_of_isMaxOn_dist hyKB hymax), hyB⟩

end InnerProduct

public section

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [FiniteDimensional ℝ E] [T2Space E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-- **Straszewicz's theorem**: in a finite-dimensional Hausdorff real topological vector space,
every extreme point of a closed convex set is a limit of exposed points. -/
theorem IsClosed.extremePoints_subset_closure_exposedPoints {K : Set E}
    (hK : IsClosed K) (hc : Convex ℝ K) : K.extremePoints ℝ ⊆ closure (K.exposedPoints ℝ) := by
  let e : E ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm
  rw [← image_subset_image_iff e.injective, image_extremePoints,
    e.image_closure, e.image_exposedPoints]
  exact extremePoints_subset_closure_exposedPoints_inner (e.isClosed_image.mpr hK)
    (hc.linear_image e.toLinearMap)

/-- In a finite-dimensional Hausdorff real topological vector space, the exposed and
extreme points of a closed convex set have the same closure. -/
theorem IsClosed.closure_exposedPoints {K : Set E} (hK : IsClosed K) (hc : Convex ℝ K) :
    closure (K.exposedPoints ℝ) = closure (K.extremePoints ℝ) :=
  (closure_mono exposedPoints_subset_extremePoints).antisymm <|
    closure_minimal (hK.extremePoints_subset_closure_exposedPoints hc) isClosed_closure
