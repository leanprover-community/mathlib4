/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Yury Kudryashov
-/
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Strict
import Mathlib.Topology.PathConnected
import Mathlib.Topology.Algebra.Affine
import Mathlib.Topology.Algebra.Module.Basic

#align_import analysis.convex.topology from "leanprover-community/mathlib"@"0e3aacdc98d25e0afe035c452d876d28cbffaa7e"

/-!
# Topological properties of convex sets

We prove the following facts:

* `Convex.interior` : interior of a convex set is convex;
* `Convex.closure` : closure of a convex set is convex;
* `Set.Finite.isCompact_convexHull` : convex hull of a finite set is compact;
* `Set.Finite.isClosed_convexHull` : convex hull of a finite set is closed.
-/

assert_not_exists Norm

open Metric Set Pointwise Convex

variable {ι 𝕜 E : Type*}

theorem Real.convex_iff_isPreconnected {s : Set ℝ} : Convex ℝ s ↔ IsPreconnected s :=
  convex_iff_ordConnected.trans isPreconnected_iff_ordConnected.symm
#align real.convex_iff_is_preconnected Real.convex_iff_isPreconnected

alias Real.convex_iff_isPreconnected ↔ _ IsPreconnected.convex
#align is_preconnected.convex IsPreconnected.convex

/-! ### Standard simplex -/


section stdSimplex

variable [Fintype ι]

/-- Every vector in `stdSimplex 𝕜 ι` has `max`-norm at most `1`. -/
theorem stdSimplex_subset_closedBall : stdSimplex ℝ ι ⊆ Metric.closedBall 0 1 := by
  intro f hf
  rw [Metric.mem_closedBall, dist_pi_le_iff zero_le_one]
  intro x
  rw [Pi.zero_apply, Real.dist_0_eq_abs, abs_of_nonneg <| hf.1 x]
  exact (mem_Icc_of_mem_stdSimplex hf x).2
#align std_simplex_subset_closed_ball stdSimplex_subset_closedBall

variable (ι)

/-- `stdSimplex ℝ ι` is bounded. -/
theorem bounded_stdSimplex : Metric.Bounded (stdSimplex ℝ ι) :=
  (Metric.bounded_iff_subset_ball 0).2 ⟨1, stdSimplex_subset_closedBall⟩
#align bounded_std_simplex bounded_stdSimplex

/-- `stdSimplex ℝ ι` is closed. -/
theorem isClosed_stdSimplex : IsClosed (stdSimplex ℝ ι) :=
  (stdSimplex_eq_inter ℝ ι).symm ▸
    IsClosed.inter (isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i))
      (isClosed_eq (continuous_finset_sum _ fun x _ => continuous_apply x) continuous_const)
#align is_closed_std_simplex isClosed_stdSimplex

/-- `stdSimplex ℝ ι` is compact. -/
theorem isCompact_stdSimplex : IsCompact (stdSimplex ℝ ι) :=
  Metric.isCompact_iff_isClosed_bounded.2 ⟨isClosed_stdSimplex ι, bounded_stdSimplex ι⟩
#align is_compact_std_simplex isCompact_stdSimplex

end stdSimplex

/-! ### Topological vector space -/


section TopologicalSpace

variable [LinearOrderedRing 𝕜] [DenselyOrdered 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜]
  [AddCommGroup E] [TopologicalSpace E] [ContinuousAdd E] [Module 𝕜 E] [ContinuousSMul 𝕜 E]
  {x y : E}

theorem segment_subset_closure_openSegment : [x -[𝕜] y] ⊆ closure (openSegment 𝕜 x y) := by
  rw [segment_eq_image, openSegment_eq_image, ← closure_Ioo (zero_ne_one' 𝕜)]
  exact image_closure_subset_closure_image (by continuity)
#align segment_subset_closure_open_segment segment_subset_closure_openSegment

end TopologicalSpace

section PseudoMetricSpace

variable [LinearOrderedRing 𝕜] [DenselyOrdered 𝕜] [PseudoMetricSpace 𝕜] [OrderTopology 𝕜]
  [ProperSpace 𝕜] [CompactIccSpace 𝕜] [AddCommGroup E] [TopologicalSpace E] [T2Space E]
  [ContinuousAdd E] [Module 𝕜 E] [ContinuousSMul 𝕜 E]

@[simp]
theorem closure_openSegment (x y : E) : closure (openSegment 𝕜 x y) = [x -[𝕜] y] := by
  rw [segment_eq_image, openSegment_eq_image, ← closure_Ioo (zero_ne_one' 𝕜)]
  exact
    (image_closure_of_isCompact (bounded_Ioo _ _).isCompact_closure <|
        Continuous.continuousOn <| by continuity).symm
#align closure_open_segment closure_openSegment

end PseudoMetricSpace

section ContinuousConstSMul

variable [LinearOrderedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [TopologicalAddGroup E] [ContinuousConstSMul 𝕜 E]

/-- If `s` is a convex set, then `a • interior s + b • closure s ⊆ interior s` for all `0 < a`,
`0 ≤ b`, `a + b = 1`. See also `Convex.combo_interior_self_subset_interior` for a weaker version. -/
theorem Convex.combo_interior_closure_subset_interior {s : Set E} (hs : Convex 𝕜 s) {a b : 𝕜}
    (ha : 0 < a) (hb : 0 ≤ b) (hab : a + b = 1) : a • interior s + b • closure s ⊆ interior s :=
  interior_smul₀ ha.ne' s ▸
    calc
      interior (a • s) + b • closure s ⊆ interior (a • s) + closure (b • s) :=
        add_subset_add Subset.rfl (smul_closure_subset b s)
      _ = interior (a • s) + b • s := by rw [isOpen_interior.add_closure (b • s)]
      _ ⊆ interior (a • s + b • s) := subset_interior_add_left
      _ ⊆ interior s := interior_mono <| hs.set_combo_subset ha.le hb hab

#align convex.combo_interior_closure_subset_interior Convex.combo_interior_closure_subset_interior

/-- If `s` is a convex set, then `a • interior s + b • s ⊆ interior s` for all `0 < a`, `0 ≤ b`,
`a + b = 1`. See also `Convex.combo_interior_closure_subset_interior` for a stronger version. -/
theorem Convex.combo_interior_self_subset_interior {s : Set E} (hs : Convex 𝕜 s) {a b : 𝕜}
    (ha : 0 < a) (hb : 0 ≤ b) (hab : a + b = 1) : a • interior s + b • s ⊆ interior s :=
  calc
    a • interior s + b • s ⊆ a • interior s + b • closure s :=
      add_subset_add Subset.rfl <| image_subset _ subset_closure
    _ ⊆ interior s := hs.combo_interior_closure_subset_interior ha hb hab

#align convex.combo_interior_self_subset_interior Convex.combo_interior_self_subset_interior

/-- If `s` is a convex set, then `a • closure s + b • interior s ⊆ interior s` for all `0 ≤ a`,
`0 < b`, `a + b = 1`. See also `Convex.combo_self_interior_subset_interior` for a weaker version. -/
theorem Convex.combo_closure_interior_subset_interior {s : Set E} (hs : Convex 𝕜 s) {a b : 𝕜}
    (ha : 0 ≤ a) (hb : 0 < b) (hab : a + b = 1) : a • closure s + b • interior s ⊆ interior s := by
  rw [add_comm]
  exact hs.combo_interior_closure_subset_interior hb ha (add_comm a b ▸ hab)
#align convex.combo_closure_interior_subset_interior Convex.combo_closure_interior_subset_interior

/-- If `s` is a convex set, then `a • s + b • interior s ⊆ interior s` for all `0 ≤ a`, `0 < b`,
`a + b = 1`. See also `Convex.combo_closure_interior_subset_interior` for a stronger version. -/
theorem Convex.combo_self_interior_subset_interior {s : Set E} (hs : Convex 𝕜 s) {a b : 𝕜}
    (ha : 0 ≤ a) (hb : 0 < b) (hab : a + b = 1) : a • s + b • interior s ⊆ interior s := by
  rw [add_comm]
  exact hs.combo_interior_self_subset_interior hb ha (add_comm a b ▸ hab)
#align convex.combo_self_interior_subset_interior Convex.combo_self_interior_subset_interior

theorem Convex.combo_interior_closure_mem_interior {s : Set E} (hs : Convex 𝕜 s) {x y : E}
    (hx : x ∈ interior s) (hy : y ∈ closure s) {a b : 𝕜} (ha : 0 < a) (hb : 0 ≤ b)
    (hab : a + b = 1) : a • x + b • y ∈ interior s :=
  hs.combo_interior_closure_subset_interior ha hb hab <|
    add_mem_add (smul_mem_smul_set hx) (smul_mem_smul_set hy)
#align convex.combo_interior_closure_mem_interior Convex.combo_interior_closure_mem_interior

theorem Convex.combo_interior_self_mem_interior {s : Set E} (hs : Convex 𝕜 s) {x y : E}
    (hx : x ∈ interior s) (hy : y ∈ s) {a b : 𝕜} (ha : 0 < a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a • x + b • y ∈ interior s :=
  hs.combo_interior_closure_mem_interior hx (subset_closure hy) ha hb hab
#align convex.combo_interior_self_mem_interior Convex.combo_interior_self_mem_interior

theorem Convex.combo_closure_interior_mem_interior {s : Set E} (hs : Convex 𝕜 s) {x y : E}
    (hx : x ∈ closure s) (hy : y ∈ interior s) {a b : 𝕜} (ha : 0 ≤ a) (hb : 0 < b)
    (hab : a + b = 1) : a • x + b • y ∈ interior s :=
  hs.combo_closure_interior_subset_interior ha hb hab <|
    add_mem_add (smul_mem_smul_set hx) (smul_mem_smul_set hy)
#align convex.combo_closure_interior_mem_interior Convex.combo_closure_interior_mem_interior

theorem Convex.combo_self_interior_mem_interior {s : Set E} (hs : Convex 𝕜 s) {x y : E} (hx : x ∈ s)
    (hy : y ∈ interior s) {a b : 𝕜} (ha : 0 ≤ a) (hb : 0 < b) (hab : a + b = 1) :
    a • x + b • y ∈ interior s :=
  hs.combo_closure_interior_mem_interior (subset_closure hx) hy ha hb hab
#align convex.combo_self_interior_mem_interior Convex.combo_self_interior_mem_interior

theorem Convex.openSegment_interior_closure_subset_interior {s : Set E} (hs : Convex 𝕜 s) {x y : E}
    (hx : x ∈ interior s) (hy : y ∈ closure s) : openSegment 𝕜 x y ⊆ interior s := by
  rintro _ ⟨a, b, ha, hb, hab, rfl⟩
  exact hs.combo_interior_closure_mem_interior hx hy ha hb.le hab
#align convex.open_segment_interior_closure_subset_interior Convex.openSegment_interior_closure_subset_interior

theorem Convex.openSegment_interior_self_subset_interior {s : Set E} (hs : Convex 𝕜 s) {x y : E}
    (hx : x ∈ interior s) (hy : y ∈ s) : openSegment 𝕜 x y ⊆ interior s :=
  hs.openSegment_interior_closure_subset_interior hx (subset_closure hy)
#align convex.open_segment_interior_self_subset_interior Convex.openSegment_interior_self_subset_interior

theorem Convex.openSegment_closure_interior_subset_interior {s : Set E} (hs : Convex 𝕜 s) {x y : E}
    (hx : x ∈ closure s) (hy : y ∈ interior s) : openSegment 𝕜 x y ⊆ interior s := by
  rintro _ ⟨a, b, ha, hb, hab, rfl⟩
  exact hs.combo_closure_interior_mem_interior hx hy ha.le hb hab
#align convex.open_segment_closure_interior_subset_interior Convex.openSegment_closure_interior_subset_interior

theorem Convex.openSegment_self_interior_subset_interior {s : Set E} (hs : Convex 𝕜 s) {x y : E}
    (hx : x ∈ s) (hy : y ∈ interior s) : openSegment 𝕜 x y ⊆ interior s :=
  hs.openSegment_closure_interior_subset_interior (subset_closure hx) hy
#align convex.open_segment_self_interior_subset_interior Convex.openSegment_self_interior_subset_interior

/-- If `x ∈ closure s` and `y ∈ interior s`, then the segment `(x, y]` is included in `interior s`.
-/
theorem Convex.add_smul_sub_mem_interior' {s : Set E} (hs : Convex 𝕜 s) {x y : E}
    (hx : x ∈ closure s) (hy : y ∈ interior s) {t : 𝕜} (ht : t ∈ Ioc (0 : 𝕜) 1) :
    x + t • (y - x) ∈ interior s := by
  simpa only [sub_smul, smul_sub, one_smul, add_sub, add_comm] using
    hs.combo_interior_closure_mem_interior hy hx ht.1 (sub_nonneg.mpr ht.2)
      (add_sub_cancel'_right _ _)
#align convex.add_smul_sub_mem_interior' Convex.add_smul_sub_mem_interior'

/-- If `x ∈ s` and `y ∈ interior s`, then the segment `(x, y]` is included in `interior s`. -/
theorem Convex.add_smul_sub_mem_interior {s : Set E} (hs : Convex 𝕜 s) {x y : E} (hx : x ∈ s)
    (hy : y ∈ interior s) {t : 𝕜} (ht : t ∈ Ioc (0 : 𝕜) 1) : x + t • (y - x) ∈ interior s :=
  hs.add_smul_sub_mem_interior' (subset_closure hx) hy ht
#align convex.add_smul_sub_mem_interior Convex.add_smul_sub_mem_interior

/-- If `x ∈ closure s` and `x + y ∈ interior s`, then `x + t y ∈ interior s` for `t ∈ (0, 1]`. -/
theorem Convex.add_smul_mem_interior' {s : Set E} (hs : Convex 𝕜 s) {x y : E} (hx : x ∈ closure s)
    (hy : x + y ∈ interior s) {t : 𝕜} (ht : t ∈ Ioc (0 : 𝕜) 1) : x + t • y ∈ interior s := by
  simpa only [add_sub_cancel'] using hs.add_smul_sub_mem_interior' hx hy ht
#align convex.add_smul_mem_interior' Convex.add_smul_mem_interior'

/-- If `x ∈ s` and `x + y ∈ interior s`, then `x + t y ∈ interior s` for `t ∈ (0, 1]`. -/
theorem Convex.add_smul_mem_interior {s : Set E} (hs : Convex 𝕜 s) {x y : E} (hx : x ∈ s)
    (hy : x + y ∈ interior s) {t : 𝕜} (ht : t ∈ Ioc (0 : 𝕜) 1) : x + t • y ∈ interior s :=
  hs.add_smul_mem_interior' (subset_closure hx) hy ht
#align convex.add_smul_mem_interior Convex.add_smul_mem_interior

/-- In a topological vector space, the interior of a convex set is convex. -/
protected theorem Convex.interior {s : Set E} (hs : Convex 𝕜 s) : Convex 𝕜 (interior s) :=
  convex_iff_openSegment_subset.mpr fun _ hx _ hy =>
    hs.openSegment_closure_interior_subset_interior (interior_subset_closure hx) hy
#align convex.interior Convex.interior

/-- In a topological vector space, the closure of a convex set is convex. -/
protected theorem Convex.closure {s : Set E} (hs : Convex 𝕜 s) : Convex 𝕜 (closure s) :=
  fun x hx y hy a b ha hb hab =>
  let f : E → E → E := fun x' y' => a • x' + b • y'
  have hf : Continuous (Function.uncurry f) :=
    (continuous_fst.const_smul _).add (continuous_snd.const_smul _)
  show f x y ∈ closure s from map_mem_closure₂ hf hx hy fun _ hx' _ hy' => hs hx' hy' ha hb hab
#align convex.closure Convex.closure

open AffineMap

/-- A convex set `s` is strictly convex provided that for any two distinct points of
`s \ interior s`, the line passing through these points has nonempty intersection with
`interior s`. -/
protected theorem Convex.strictConvex' {s : Set E} (hs : Convex 𝕜 s)
    (h : (s \ interior s).Pairwise fun x y => ∃ c : 𝕜, lineMap x y c ∈ interior s) :
    StrictConvex 𝕜 s := by
  refine' strictConvex_iff_openSegment_subset.2 _
  intro x hx y hy hne
  by_cases hx' : x ∈ interior s
  · exact hs.openSegment_interior_self_subset_interior hx' hy
  by_cases hy' : y ∈ interior s
  · exact hs.openSegment_self_interior_subset_interior hx hy'
  rcases h ⟨hx, hx'⟩ ⟨hy, hy'⟩ hne with ⟨c, hc⟩
  refine' (openSegment_subset_union x y ⟨c, rfl⟩).trans (insert_subset_iff.2 ⟨hc, union_subset _ _⟩)
  exacts [hs.openSegment_self_interior_subset_interior hx hc,
    hs.openSegment_interior_self_subset_interior hc hy]
#align convex.strict_convex' Convex.strictConvex'

/-- A convex set `s` is strictly convex provided that for any two distinct points `x`, `y` of
`s \ interior s`, the segment with endpoints `x`, `y` has nonempty intersection with
`interior s`. -/
protected theorem Convex.strictConvex {s : Set E} (hs : Convex 𝕜 s)
    (h : (s \ interior s).Pairwise fun x y => ([x -[𝕜] y] \ frontier s).Nonempty) :
    StrictConvex 𝕜 s := by
  refine' hs.strictConvex' <| h.imp_on fun x hx y hy _ => _
  simp only [segment_eq_image_lineMap, ← self_diff_frontier]
  rintro ⟨_, ⟨⟨c, hc, rfl⟩, hcs⟩⟩
  refine' ⟨c, hs.segment_subset hx.1 hy.1 _, hcs⟩
  exact (segment_eq_image_lineMap 𝕜 x y).symm ▸ mem_image_of_mem _ hc
#align convex.strict_convex Convex.strictConvex

end ContinuousConstSMul

section ContinuousSMul

variable [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [TopologicalAddGroup E]
  [ContinuousSMul ℝ E]

/-- Convex hull of a finite set is compact. -/
theorem Set.Finite.isCompact_convexHull {s : Set E} (hs : s.Finite) :
    IsCompact (convexHull ℝ s) := by
  rw [hs.convexHull_eq_image]
  apply (@isCompact_stdSimplex _ hs.fintype).image
  haveI := hs.fintype
  apply LinearMap.continuous_on_pi
#align set.finite.compact_convex_hull Set.Finite.isCompact_convexHull

/-- Convex hull of a finite set is closed. -/
theorem Set.Finite.isClosed_convexHull [T2Space E] {s : Set E} (hs : s.Finite) :
    IsClosed (convexHull ℝ s) :=
  hs.isCompact_convexHull.isClosed
#align set.finite.is_closed_convex_hull Set.Finite.isClosed_convexHull

open AffineMap

/-- If we dilate the interior of a convex set about a point in its interior by a scale `t > 1`,
the result includes the closure of the original set.

TODO Generalise this from convex sets to sets that are balanced / star-shaped about `x`. -/
theorem Convex.closure_subset_image_homothety_interior_of_one_lt {s : Set E} (hs : Convex ℝ s)
    {x : E} (hx : x ∈ interior s) (t : ℝ) (ht : 1 < t) :
    closure s ⊆ homothety x t '' interior s := by
  intro y hy
  have hne : t ≠ 0 := (one_pos.trans ht).ne'
  refine'
    ⟨homothety x t⁻¹ y, hs.openSegment_interior_closure_subset_interior hx hy _,
      (AffineEquiv.homothetyUnitsMulHom x (Units.mk0 t hne)).apply_symm_apply y⟩
  rw [openSegment_eq_image_lineMap, ← inv_one, ← inv_Ioi (zero_lt_one' ℝ), ← image_inv, image_image,
    homothety_eq_lineMap]
  exact mem_image_of_mem _ ht
#align convex.closure_subset_image_homothety_interior_of_one_lt Convex.closure_subset_image_homothety_interior_of_one_lt

/-- If we dilate a convex set about a point in its interior by a scale `t > 1`, the interior of
the result includes the closure of the original set.

TODO Generalise this from convex sets to sets that are balanced / star-shaped about `x`. -/
theorem Convex.closure_subset_interior_image_homothety_of_one_lt {s : Set E} (hs : Convex ℝ s)
    {x : E} (hx : x ∈ interior s) (t : ℝ) (ht : 1 < t) :
    closure s ⊆ interior (homothety x t '' s) :=
  (hs.closure_subset_image_homothety_interior_of_one_lt hx t ht).trans <|
    (homothety_isOpenMap x t (one_pos.trans ht).ne').image_interior_subset _
#align convex.closure_subset_interior_image_homothety_of_one_lt Convex.closure_subset_interior_image_homothety_of_one_lt

/-- If we dilate a convex set about a point in its interior by a scale `t > 1`, the interior of
the result includes the closure of the original set.

TODO Generalise this from convex sets to sets that are balanced / star-shaped about `x`. -/
theorem Convex.subset_interior_image_homothety_of_one_lt {s : Set E} (hs : Convex ℝ s) {x : E}
    (hx : x ∈ interior s) (t : ℝ) (ht : 1 < t) : s ⊆ interior (homothety x t '' s) :=
  subset_closure.trans <| hs.closure_subset_interior_image_homothety_of_one_lt hx t ht
#align convex.subset_interior_image_homothety_of_one_lt Convex.subset_interior_image_homothety_of_one_lt

/-- A nonempty convex set is path connected. -/
protected theorem Convex.isPathConnected {s : Set E} (hconv : Convex ℝ s) (hne : s.Nonempty) :
    IsPathConnected s := by
  refine' isPathConnected_iff.mpr ⟨hne, _⟩
  intro x x_in y y_in
  have H := hconv.segment_subset x_in y_in
  rw [segment_eq_image_lineMap] at H
  exact
    JoinedIn.ofLine AffineMap.lineMap_continuous.continuousOn (lineMap_apply_zero _ _)
      (lineMap_apply_one _ _) H
#align convex.is_path_connected Convex.isPathConnected

/-- A nonempty convex set is connected. -/
protected theorem Convex.isConnected {s : Set E} (h : Convex ℝ s) (hne : s.Nonempty) :
    IsConnected s :=
  (h.isPathConnected hne).isConnected
#align convex.is_connected Convex.isConnected

/-- A convex set is preconnected. -/
protected theorem Convex.isPreconnected {s : Set E} (h : Convex ℝ s) : IsPreconnected s :=
  s.eq_empty_or_nonempty.elim (fun h => h.symm ▸ isPreconnected_empty) fun hne =>
    (h.isConnected hne).isPreconnected
#align convex.is_preconnected Convex.isPreconnected

/-- Every topological vector space over ℝ is path connected.

Not an instance, because it creates enormous TC subproblems (turn on `pp.all`).
-/
protected theorem TopologicalAddGroup.pathConnectedSpace : PathConnectedSpace E :=
  pathConnectedSpace_iff_univ.mpr <| convex_univ.isPathConnected ⟨(0 : E), trivial⟩
#align topological_add_group.path_connected TopologicalAddGroup.pathConnectedSpace

end ContinuousSMul
