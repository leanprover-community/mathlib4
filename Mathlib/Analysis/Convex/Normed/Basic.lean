/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Yury Kudryashov
-/
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Normed.Module.Basic

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

variable {E : Type*}

open Set

section SeminormedAddCommGroup
variable [SeminormedAddCommGroup E] [NormedSpace ℝ E]
variable {s : Set E}

/-- The norm on a real normed space is convex on any convex set. See also `Seminorm.convexOn`
and `convexOn_univ_norm`. -/
theorem convexOn_norm (hs : Convex ℝ s) : ConvexOn ℝ s norm :=
  ⟨hs, fun x _ y _ a b ha hb _ =>
    calc
      ‖a • x + b • y‖ ≤ ‖a • x‖ + ‖b • y‖ := norm_add_le _ _
      _ = a * ‖x‖ + b * ‖y‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]⟩

/-- The norm on a real normed space is convex on the whole space. See also `Seminorm.convexOn`
and `convexOn_norm`. -/
theorem convexOn_univ_norm : ConvexOn ℝ univ (norm : E → ℝ) :=
  convexOn_norm convex_univ

theorem convexOn_dist (z : E) (hs : Convex ℝ s) : ConvexOn ℝ s fun z' => dist z' z := by
  simpa [dist_eq_norm, preimage_preimage] using
    (convexOn_norm (hs.translate (-z))).comp_affineMap (AffineMap.id ℝ E - AffineMap.const ℝ E z)

theorem convexOn_univ_dist (z : E) : ConvexOn ℝ univ fun z' => dist z' z :=
  convexOn_dist z convex_univ

theorem convex_ball (a : E) (r : ℝ) : Convex ℝ (Metric.ball a r) := by
  simpa only [Metric.ball, sep_univ] using (convexOn_univ_dist a).convex_lt r

theorem convex_closedBall (a : E) (r : ℝ) : Convex ℝ (Metric.closedBall a r) := by
  simpa only [Metric.closedBall, sep_univ] using (convexOn_univ_dist a).convex_le r

/-- Given a point `x` in the convex hull of `s` and a point `y`, there exists a point
of `s` at distance at least `dist x y` from `y`. -/
theorem convexHull_exists_dist_ge {s : Set E} {x : E} (hx : x ∈ convexHull ℝ s) (y : E) :
    ∃ x' ∈ s, dist x y ≤ dist x' y :=
  (convexOn_dist y (convex_convexHull ℝ _)).exists_ge_of_mem_convexHull (subset_convexHull ..) hx

/-- Given a point `x` in the convex hull of `s` and a point `y` in the convex hull of `t`,
there exist points `x' ∈ s` and `y' ∈ t` at distance at least `dist x y`. -/
theorem convexHull_exists_dist_ge2 {s t : Set E} {x y : E} (hx : x ∈ convexHull ℝ s)
    (hy : y ∈ convexHull ℝ t) : ∃ x' ∈ s, ∃ y' ∈ t, dist x y ≤ dist x' y' := by
  rcases convexHull_exists_dist_ge hx y with ⟨x', hx', Hx'⟩
  rcases convexHull_exists_dist_ge hy x' with ⟨y', hy', Hy'⟩
  use x', hx', y', hy'
  exact le_trans Hx' (dist_comm y x' ▸ dist_comm y' x' ▸ Hy')

/-- Emetric diameter of the convex hull of a set `s` equals the emetric diameter of `s`. -/
@[simp]
theorem convexHull_ediam (s : Set E) : EMetric.diam (convexHull ℝ s) = EMetric.diam s := by
  refine (EMetric.diam_le fun x hx y hy => ?_).antisymm (EMetric.diam_mono <| subset_convexHull ℝ s)
  rcases convexHull_exists_dist_ge2 hx hy with ⟨x', hx', y', hy', H⟩
  rw [edist_dist]
  apply le_trans (ENNReal.ofReal_le_ofReal H)
  rw [← edist_dist]
  exact EMetric.edist_le_diam_of_mem hx' hy'

/-- Diameter of the convex hull of a set `s` equals the emetric diameter of `s`. -/
@[simp]
theorem convexHull_diam (s : Set E) : Metric.diam (convexHull ℝ s) = Metric.diam s := by
  simp only [Metric.diam, convexHull_ediam]

/-- Convex hull of `s` is bounded if and only if `s` is bounded. -/
@[simp]
theorem isBounded_convexHull {s : Set E} :
    Bornology.IsBounded (convexHull ℝ s) ↔ Bornology.IsBounded s := by
  simp only [Metric.isBounded_iff_ediam_ne_top, convexHull_ediam]

end SeminormedAddCommGroup
