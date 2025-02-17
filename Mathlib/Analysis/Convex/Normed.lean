/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Yury Kudryashov
-/
import Mathlib.Analysis.Convex.Between
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Group.Pointwise
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Analysis.Normed.Affine.AddTorsorBases

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

variable {E P : Type*}

open AffineBasis Module Metric Set
open scoped Convex Pointwise Topology

section SeminormedAddCommGroup
variable [SeminormedAddCommGroup E] [NormedSpace ℝ E] [PseudoMetricSpace P] [NormedAddTorsor E P]
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

theorem Convex.thickening (hs : Convex ℝ s) (δ : ℝ) : Convex ℝ (thickening δ s) := by
  rw [← add_ball_zero]
  exact hs.add (convex_ball 0 _)

theorem Convex.cthickening (hs : Convex ℝ s) (δ : ℝ) : Convex ℝ (cthickening δ s) := by
  obtain hδ | hδ := le_total 0 δ
  · rw [cthickening_eq_iInter_thickening hδ]
    exact convex_iInter₂ fun _ _ => hs.thickening _
  · rw [cthickening_of_nonpos hδ]
    exact hs.closure

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

instance (priority := 100) NormedSpace.instPathConnectedSpace : PathConnectedSpace E :=
  IsTopologicalAddGroup.pathConnectedSpace

theorem Wbtw.dist_add_dist {x y z : P} (h : Wbtw ℝ x y z) :
    dist x y + dist y z = dist x z := by
  obtain ⟨a, ⟨ha₀, ha₁⟩, rfl⟩ := h
  simp [abs_of_nonneg, ha₀, ha₁, sub_mul]

theorem dist_add_dist_of_mem_segment {x y z : E} (h : y ∈ [x -[ℝ] z]) :
    dist x y + dist y z = dist x z :=
  (mem_segment_iff_wbtw.1 h).dist_add_dist

/-- The set of vectors in the same ray as `x` is connected. -/
theorem isConnected_setOf_sameRay (x : E) : IsConnected { y | SameRay ℝ x y } := by
  by_cases hx : x = 0; · simpa [hx] using isConnected_univ (α := E)
  simp_rw [← exists_nonneg_left_iff_sameRay hx]
  exact isConnected_Ici.image _ (continuous_id.smul continuous_const).continuousOn

/-- The set of nonzero vectors in the same ray as the nonzero vector `x` is connected. -/
theorem isConnected_setOf_sameRay_and_ne_zero {x : E} (hx : x ≠ 0) :
    IsConnected { y | SameRay ℝ x y ∧ y ≠ 0 } := by
  simp_rw [← exists_pos_left_iff_sameRay_and_ne_zero hx]
  exact isConnected_Ioi.image _ (continuous_id.smul continuous_const).continuousOn

end SeminormedAddCommGroup

section NormedAddCommGroup
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {s : Set E} {x : E}

/-- We can intercalate a simplex between a point and one of its neighborhoods. -/
lemma exists_mem_interior_convexHull_affineBasis (hs : s ∈ 𝓝 x) :
    ∃ b : AffineBasis (Fin (finrank ℝ E + 1)) ℝ E,
      x ∈ interior (convexHull ℝ (range b)) ∧ convexHull ℝ (range b) ⊆ s := by
  classical
  -- By translating, WLOG `x` is the origin.
  wlog hx : x = 0
  · obtain ⟨b, hb⟩ := this (s := -x +ᵥ s) (by simpa using vadd_mem_nhds_vadd (-x) hs) rfl
    use x +ᵥ b
    simpa [subset_vadd_set_iff, mem_vadd_set_iff_neg_vadd_mem, convexHull_vadd, interior_vadd,
      Pi.vadd_def, -vadd_eq_add, vadd_eq_add (a := -x), ← Set.vadd_set_range] using hb
  subst hx
  -- The strategy is now to find an arbitrary maximal spanning simplex (aka an affine basis)...
  obtain ⟨b⟩ := exists_affineBasis_of_finiteDimensional
    (ι := Fin (finrank ℝ E + 1)) (k := ℝ) (P := E) (by simp)
  -- ... translate it to contain the origin...
  set c : AffineBasis (Fin (finrank ℝ E + 1)) ℝ E := -Finset.univ.centroid ℝ b +ᵥ b
  have hc₀ : 0 ∈ interior (convexHull ℝ (range c) : Set E) := by
    simpa [c, convexHull_vadd, interior_vadd, range_add, Pi.vadd_def, mem_vadd_set_iff_neg_vadd_mem]
      using b.centroid_mem_interior_convexHull
  set cnorm := Finset.univ.sup' Finset.univ_nonempty (fun i ↦ ‖c i‖)
  have hcnorm : range c ⊆ closedBall 0 (cnorm + 1) := by
    simpa only [cnorm, subset_def, Finset.mem_coe, mem_closedBall, dist_zero_right,
      ← sub_le_iff_le_add, Finset.le_sup'_iff, forall_mem_range] using fun i ↦ ⟨i, by simp⟩
  -- ... and finally scale it to fit inside the neighborhood `s`.
  obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhds_iff.1 hs
  set ε' : ℝ := ε / 2 / (cnorm + 1)
  have hc' : 0 < cnorm + 1 := by
    have : 0 ≤ cnorm := Finset.le_sup'_of_le _ (Finset.mem_univ 0) (norm_nonneg _)
    positivity
  have hε' : 0 < ε' := by positivity
  set d : AffineBasis (Fin (finrank ℝ E + 1)) ℝ E := Units.mk0 ε' hε'.ne' • c
  have hε₀ : 0 < ε / 2 := by positivity
  have hdnorm : (range d : Set E) ⊆ closedBall 0 (ε / 2) := by
    simp [d, Set.smul_set_subset_iff₀ hε'.ne', hε₀.le, _root_.smul_closedBall, abs_of_nonneg hε'.le,
      range_subset_iff, norm_smul]
    simpa [ε', hε₀.ne', range_subset_iff, ← mul_div_right_comm (ε / 2), div_le_iff₀ hc',
      mul_le_mul_left hε₀] using hcnorm
  refine ⟨d, ?_, ?_⟩
  · simpa [d, Pi.smul_def, range_smul, interior_smul₀, convexHull_smul, zero_mem_smul_set_iff,
      hε'.ne']
  · calc
      convexHull ℝ (range d) ⊆ closedBall 0 (ε / 2) := convexHull_min hdnorm (convex_closedBall ..)
      _ ⊆ ball 0 ε := closedBall_subset_ball (by linarith)
      _ ⊆ s := hεs

end NormedAddCommGroup
