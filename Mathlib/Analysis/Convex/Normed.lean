/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Yury Kudryashov
-/
import Mathlib.Analysis.Convex.Between
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Group.Pointwise
import Mathlib.Analysis.NormedSpace.AddTorsor

#align_import analysis.convex.normed from "leanprover-community/mathlib"@"a63928c34ec358b5edcda2bf7513c50052a5230f"

/-!
# Topological and metric properties of convex sets in normed spaces

We prove the following facts:

* `convexOn_norm`, `convexOn_dist` : norm and distance to a fixed point is convex on any convex
  set;
* `convexOn_univ_norm`, `convexOn_univ_dist` : norm and distance to a fixed point is convex on
  the whole space;
* `convexHull_ediam`, `convexHull_diam` : convex hull of a set has the same (e)metric diameter
  as the original set;
* `bounded_convexHull` : convex hull of a set is bounded if and only if the original set
  is bounded.
-/

variable {ι : Type*} {E P : Type*}

open Metric Set
open scoped Convex

variable [SeminormedAddCommGroup E] [NormedSpace ℝ E] [PseudoMetricSpace P] [NormedAddTorsor E P]
variable {s t : Set E}

/-- The norm on a real normed space is convex on any convex set. See also `Seminorm.convexOn`
and `convexOn_univ_norm`. -/
theorem convexOn_norm (hs : Convex ℝ s) : ConvexOn ℝ s norm :=
  ⟨hs, fun x _ y _ a b ha hb _ =>
    calc
      ‖a • x + b • y‖ ≤ ‖a • x‖ + ‖b • y‖ := norm_add_le _ _
      _ = a * ‖x‖ + b * ‖y‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]⟩
#align convex_on_norm convexOn_norm

/-- The norm on a real normed space is convex on the whole space. See also `Seminorm.convexOn`
and `convexOn_norm`. -/
theorem convexOn_univ_norm : ConvexOn ℝ univ (norm : E → ℝ) :=
  convexOn_norm convex_univ
#align convex_on_univ_norm convexOn_univ_norm

theorem convexOn_dist (z : E) (hs : Convex ℝ s) : ConvexOn ℝ s fun z' => dist z' z := by
  simpa [dist_eq_norm, preimage_preimage] using
    (convexOn_norm (hs.translate (-z))).comp_affineMap (AffineMap.id ℝ E - AffineMap.const ℝ E z)
#align convex_on_dist convexOn_dist

theorem convexOn_univ_dist (z : E) : ConvexOn ℝ univ fun z' => dist z' z :=
  convexOn_dist z convex_univ
#align convex_on_univ_dist convexOn_univ_dist

theorem convex_ball (a : E) (r : ℝ) : Convex ℝ (Metric.ball a r) := by
  simpa only [Metric.ball, sep_univ] using (convexOn_univ_dist a).convex_lt r
#align convex_ball convex_ball

theorem convex_closedBall (a : E) (r : ℝ) : Convex ℝ (Metric.closedBall a r) := by
  simpa only [Metric.closedBall, sep_univ] using (convexOn_univ_dist a).convex_le r
#align convex_closed_ball convex_closedBall

theorem Convex.thickening (hs : Convex ℝ s) (δ : ℝ) : Convex ℝ (thickening δ s) := by
  rw [← add_ball_zero]
  exact hs.add (convex_ball 0 _)
#align convex.thickening Convex.thickening

theorem Convex.cthickening (hs : Convex ℝ s) (δ : ℝ) : Convex ℝ (cthickening δ s) := by
  obtain hδ | hδ := le_total 0 δ
  · rw [cthickening_eq_iInter_thickening hδ]
    exact convex_iInter₂ fun _ _ => hs.thickening _
  · rw [cthickening_of_nonpos hδ]
    exact hs.closure
#align convex.cthickening Convex.cthickening

/-- Given a point `x` in the convex hull of `s` and a point `y`, there exists a point
of `s` at distance at least `dist x y` from `y`. -/
theorem convexHull_exists_dist_ge {s : Set E} {x : E} (hx : x ∈ convexHull ℝ s) (y : E) :
    ∃ x' ∈ s, dist x y ≤ dist x' y :=
  (convexOn_dist y (convex_convexHull ℝ _)).exists_ge_of_mem_convexHull hx
#align convex_hull_exists_dist_ge convexHull_exists_dist_ge

/-- Given a point `x` in the convex hull of `s` and a point `y` in the convex hull of `t`,
there exist points `x' ∈ s` and `y' ∈ t` at distance at least `dist x y`. -/
theorem convexHull_exists_dist_ge2 {s t : Set E} {x y : E} (hx : x ∈ convexHull ℝ s)
    (hy : y ∈ convexHull ℝ t) : ∃ x' ∈ s, ∃ y' ∈ t, dist x y ≤ dist x' y' := by
  rcases convexHull_exists_dist_ge hx y with ⟨x', hx', Hx'⟩
  rcases convexHull_exists_dist_ge hy x' with ⟨y', hy', Hy'⟩
  use x', hx', y', hy'
  exact le_trans Hx' (dist_comm y x' ▸ dist_comm y' x' ▸ Hy')
#align convex_hull_exists_dist_ge2 convexHull_exists_dist_ge2

/-- Emetric diameter of the convex hull of a set `s` equals the emetric diameter of `s`. -/
@[simp]
theorem convexHull_ediam (s : Set E) : EMetric.diam (convexHull ℝ s) = EMetric.diam s := by
  refine (EMetric.diam_le fun x hx y hy => ?_).antisymm (EMetric.diam_mono <| subset_convexHull ℝ s)
  rcases convexHull_exists_dist_ge2 hx hy with ⟨x', hx', y', hy', H⟩
  rw [edist_dist]
  apply le_trans (ENNReal.ofReal_le_ofReal H)
  rw [← edist_dist]
  exact EMetric.edist_le_diam_of_mem hx' hy'
#align convex_hull_ediam convexHull_ediam

/-- Diameter of the convex hull of a set `s` equals the emetric diameter of `s`. -/
@[simp]
theorem convexHull_diam (s : Set E) : Metric.diam (convexHull ℝ s) = Metric.diam s := by
  simp only [Metric.diam, convexHull_ediam]
#align convex_hull_diam convexHull_diam

/-- Convex hull of `s` is bounded if and only if `s` is bounded. -/
@[simp]
theorem isBounded_convexHull {s : Set E} :
    Bornology.IsBounded (convexHull ℝ s) ↔ Bornology.IsBounded s := by
  simp only [Metric.isBounded_iff_ediam_ne_top, convexHull_ediam]
#align bounded_convex_hull isBounded_convexHull

instance (priority := 100) NormedSpace.instPathConnectedSpace : PathConnectedSpace E :=
  TopologicalAddGroup.pathConnectedSpace
#align normed_space.path_connected NormedSpace.instPathConnectedSpace

instance (priority := 100) NormedSpace.instLocPathConnectedSpace : LocPathConnectedSpace E :=
  locPathConnected_of_bases (fun x => Metric.nhds_basis_ball) fun x r r_pos =>
    (convex_ball x r).isPathConnected <| by simp [r_pos]
#align normed_space.loc_path_connected NormedSpace.instLocPathConnectedSpace

theorem Wbtw.dist_add_dist {x y z : P} (h : Wbtw ℝ x y z) :
    dist x y + dist y z = dist x z := by
  obtain ⟨a, ⟨ha₀, ha₁⟩, rfl⟩ := h
  simp [abs_of_nonneg, ha₀, ha₁, sub_mul]

theorem dist_add_dist_of_mem_segment {x y z : E} (h : y ∈ [x -[ℝ] z]) :
    dist x y + dist y z = dist x z :=
  (mem_segment_iff_wbtw.1 h).dist_add_dist
#align dist_add_dist_of_mem_segment dist_add_dist_of_mem_segment

/-- The set of vectors in the same ray as `x` is connected. -/
theorem isConnected_setOf_sameRay (x : E) : IsConnected { y | SameRay ℝ x y } := by
  by_cases hx : x = 0; · simpa [hx] using isConnected_univ (α := E)
  simp_rw [← exists_nonneg_left_iff_sameRay hx]
  exact isConnected_Ici.image _ (continuous_id.smul continuous_const).continuousOn
#align is_connected_set_of_same_ray isConnected_setOf_sameRay

/-- The set of nonzero vectors in the same ray as the nonzero vector `x` is connected. -/
theorem isConnected_setOf_sameRay_and_ne_zero {x : E} (hx : x ≠ 0) :
    IsConnected { y | SameRay ℝ x y ∧ y ≠ 0 } := by
  simp_rw [← exists_pos_left_iff_sameRay_and_ne_zero hx]
  exact isConnected_Ioi.image _ (continuous_id.smul continuous_const).continuousOn
#align is_connected_set_of_same_ray_and_ne_zero isConnected_setOf_sameRay_and_ne_zero
