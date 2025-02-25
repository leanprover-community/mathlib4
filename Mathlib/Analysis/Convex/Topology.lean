/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Yury Kudryashov
-/
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Strict
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Algebra.Affine
import Mathlib.Topology.Algebra.Module.Basic

/-!
# Topological properties of convex sets

We prove the following facts:

* `Convex.interior` : interior of a convex set is convex;
* `Convex.closure` : closure of a convex set is convex;
* `closedConvexHull_closure_eq_closedConvexHull` : the closed convex hull of the closure of a set is
  equal to the closed convex hull of the set;
* `Set.Finite.isCompact_convexHull` : convex hull of a finite set is compact;
* `Set.Finite.isClosed_convexHull` : convex hull of a finite set is closed.
-/

assert_not_exists Norm

open Metric Bornology Set Pointwise Convex

variable {ι 𝕜 E : Type*}

namespace Real
variable {s : Set ℝ} {r ε : ℝ}

lemma closedBall_eq_segment (hε : 0 ≤ ε) : closedBall r ε = segment ℝ (r - ε) (r + ε) := by
  rw [closedBall_eq_Icc, segment_eq_Icc ((sub_le_self _ hε).trans <| le_add_of_nonneg_right hε)]

lemma ball_eq_openSegment (hε : 0 < ε) : ball r ε = openSegment ℝ (r - ε) (r + ε) := by
  rw [ball_eq_Ioo, openSegment_eq_Ioo ((sub_lt_self _ hε).trans <| lt_add_of_pos_right _ hε)]

theorem convex_iff_isPreconnected : Convex ℝ s ↔ IsPreconnected s :=
  convex_iff_ordConnected.trans isPreconnected_iff_ordConnected.symm

end Real

alias ⟨_, IsPreconnected.convex⟩ := Real.convex_iff_isPreconnected

/-! ### Standard simplex -/


section stdSimplex

variable [Fintype ι]

/-- Every vector in `stdSimplex 𝕜 ι` has `max`-norm at most `1`. -/
theorem stdSimplex_subset_closedBall : stdSimplex ℝ ι ⊆ Metric.closedBall 0 1 := fun f hf ↦ by
  rw [Metric.mem_closedBall, dist_pi_le_iff zero_le_one]
  intro x
  rw [Pi.zero_apply, Real.dist_0_eq_abs, abs_of_nonneg <| hf.1 x]
  exact (mem_Icc_of_mem_stdSimplex hf x).2

variable (ι)

/-- `stdSimplex ℝ ι` is bounded. -/
theorem bounded_stdSimplex : IsBounded (stdSimplex ℝ ι) :=
  (Metric.isBounded_iff_subset_closedBall 0).2 ⟨1, stdSimplex_subset_closedBall⟩

/-- `stdSimplex ℝ ι` is closed. -/
theorem isClosed_stdSimplex : IsClosed (stdSimplex ℝ ι) :=
  (stdSimplex_eq_inter ℝ ι).symm ▸
    IsClosed.inter (isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i))
      (isClosed_eq (continuous_finset_sum _ fun x _ => continuous_apply x) continuous_const)

/-- `stdSimplex ℝ ι` is compact. -/
theorem isCompact_stdSimplex : IsCompact (stdSimplex ℝ ι) :=
  Metric.isCompact_iff_isClosed_bounded.2 ⟨isClosed_stdSimplex ι, bounded_stdSimplex ι⟩

instance stdSimplex.instCompactSpace_coe : CompactSpace ↥(stdSimplex ℝ ι) :=
  isCompact_iff_compactSpace.mp <| isCompact_stdSimplex _

/-- The standard one-dimensional simplex in `ℝ² = Fin 2 → ℝ`
is homeomorphic to the unit interval. -/
@[simps! (config := .asFn)]
def stdSimplexHomeomorphUnitInterval : stdSimplex ℝ (Fin 2) ≃ₜ unitInterval where
  toEquiv := stdSimplexEquivIcc ℝ
  continuous_toFun := .subtype_mk ((continuous_apply 0).comp continuous_subtype_val) _
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (continuous_pi <| Fin.forall_fin_two.2
      ⟨continuous_subtype_val, continuous_const.sub continuous_subtype_val⟩)

end stdSimplex

/-! ### Topological vector spaces -/
section TopologicalSpace

variable [LinearOrderedRing 𝕜] [DenselyOrdered 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜]
  [AddCommGroup E] [TopologicalSpace E] [ContinuousAdd E] [Module 𝕜 E] [ContinuousSMul 𝕜 E]
  {x y : E}

theorem segment_subset_closure_openSegment : [x -[𝕜] y] ⊆ closure (openSegment 𝕜 x y) := by
  rw [segment_eq_image, openSegment_eq_image, ← closure_Ioo (zero_ne_one' 𝕜)]
  exact image_closure_subset_closure_image (by fun_prop)

end TopologicalSpace

section PseudoMetricSpace

variable [LinearOrderedRing 𝕜] [DenselyOrdered 𝕜] [PseudoMetricSpace 𝕜] [OrderTopology 𝕜]
  [ProperSpace 𝕜] [CompactIccSpace 𝕜] [AddCommGroup E] [TopologicalSpace E] [T2Space E]
  [ContinuousAdd E] [Module 𝕜 E] [ContinuousSMul 𝕜 E]

@[simp]
theorem closure_openSegment (x y : E) : closure (openSegment 𝕜 x y) = [x -[𝕜] y] := by
  rw [segment_eq_image, openSegment_eq_image, ← closure_Ioo (zero_ne_one' 𝕜)]
  exact (image_closure_of_isCompact (isBounded_Ioo _ _).isCompact_closure <|
    Continuous.continuousOn <| by fun_prop).symm

end PseudoMetricSpace

section ContinuousConstSMul

variable [LinearOrderedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousConstSMul 𝕜 E]

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

/-- If `s` is a convex set, then `a • interior s + b • s ⊆ interior s` for all `0 < a`, `0 ≤ b`,
`a + b = 1`. See also `Convex.combo_interior_closure_subset_interior` for a stronger version. -/
theorem Convex.combo_interior_self_subset_interior {s : Set E} (hs : Convex 𝕜 s) {a b : 𝕜}
    (ha : 0 < a) (hb : 0 ≤ b) (hab : a + b = 1) : a • interior s + b • s ⊆ interior s :=
  calc
    a • interior s + b • s ⊆ a • interior s + b • closure s :=
      add_subset_add Subset.rfl <| image_subset _ subset_closure
    _ ⊆ interior s := hs.combo_interior_closure_subset_interior ha hb hab

/-- If `s` is a convex set, then `a • closure s + b • interior s ⊆ interior s` for all `0 ≤ a`,
`0 < b`, `a + b = 1`. See also `Convex.combo_self_interior_subset_interior` for a weaker version. -/
theorem Convex.combo_closure_interior_subset_interior {s : Set E} (hs : Convex 𝕜 s) {a b : 𝕜}
    (ha : 0 ≤ a) (hb : 0 < b) (hab : a + b = 1) : a • closure s + b • interior s ⊆ interior s := by
  rw [add_comm]
  exact hs.combo_interior_closure_subset_interior hb ha (add_comm a b ▸ hab)

/-- If `s` is a convex set, then `a • s + b • interior s ⊆ interior s` for all `0 ≤ a`, `0 < b`,
`a + b = 1`. See also `Convex.combo_closure_interior_subset_interior` for a stronger version. -/
theorem Convex.combo_self_interior_subset_interior {s : Set E} (hs : Convex 𝕜 s) {a b : 𝕜}
    (ha : 0 ≤ a) (hb : 0 < b) (hab : a + b = 1) : a • s + b • interior s ⊆ interior s := by
  rw [add_comm]
  exact hs.combo_interior_self_subset_interior hb ha (add_comm a b ▸ hab)

theorem Convex.combo_interior_closure_mem_interior {s : Set E} (hs : Convex 𝕜 s) {x y : E}
    (hx : x ∈ interior s) (hy : y ∈ closure s) {a b : 𝕜} (ha : 0 < a) (hb : 0 ≤ b)
    (hab : a + b = 1) : a • x + b • y ∈ interior s :=
  hs.combo_interior_closure_subset_interior ha hb hab <|
    add_mem_add (smul_mem_smul_set hx) (smul_mem_smul_set hy)

theorem Convex.combo_interior_self_mem_interior {s : Set E} (hs : Convex 𝕜 s) {x y : E}
    (hx : x ∈ interior s) (hy : y ∈ s) {a b : 𝕜} (ha : 0 < a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a • x + b • y ∈ interior s :=
  hs.combo_interior_closure_mem_interior hx (subset_closure hy) ha hb hab

theorem Convex.combo_closure_interior_mem_interior {s : Set E} (hs : Convex 𝕜 s) {x y : E}
    (hx : x ∈ closure s) (hy : y ∈ interior s) {a b : 𝕜} (ha : 0 ≤ a) (hb : 0 < b)
    (hab : a + b = 1) : a • x + b • y ∈ interior s :=
  hs.combo_closure_interior_subset_interior ha hb hab <|
    add_mem_add (smul_mem_smul_set hx) (smul_mem_smul_set hy)

theorem Convex.combo_self_interior_mem_interior {s : Set E} (hs : Convex 𝕜 s) {x y : E} (hx : x ∈ s)
    (hy : y ∈ interior s) {a b : 𝕜} (ha : 0 ≤ a) (hb : 0 < b) (hab : a + b = 1) :
    a • x + b • y ∈ interior s :=
  hs.combo_closure_interior_mem_interior (subset_closure hx) hy ha hb hab

theorem Convex.openSegment_interior_closure_subset_interior {s : Set E} (hs : Convex 𝕜 s) {x y : E}
    (hx : x ∈ interior s) (hy : y ∈ closure s) : openSegment 𝕜 x y ⊆ interior s := by
  rintro _ ⟨a, b, ha, hb, hab, rfl⟩
  exact hs.combo_interior_closure_mem_interior hx hy ha hb.le hab

theorem Convex.openSegment_interior_self_subset_interior {s : Set E} (hs : Convex 𝕜 s) {x y : E}
    (hx : x ∈ interior s) (hy : y ∈ s) : openSegment 𝕜 x y ⊆ interior s :=
  hs.openSegment_interior_closure_subset_interior hx (subset_closure hy)

theorem Convex.openSegment_closure_interior_subset_interior {s : Set E} (hs : Convex 𝕜 s) {x y : E}
    (hx : x ∈ closure s) (hy : y ∈ interior s) : openSegment 𝕜 x y ⊆ interior s := by
  rintro _ ⟨a, b, ha, hb, hab, rfl⟩
  exact hs.combo_closure_interior_mem_interior hx hy ha.le hb hab

theorem Convex.openSegment_self_interior_subset_interior {s : Set E} (hs : Convex 𝕜 s) {x y : E}
    (hx : x ∈ s) (hy : y ∈ interior s) : openSegment 𝕜 x y ⊆ interior s :=
  hs.openSegment_closure_interior_subset_interior (subset_closure hx) hy

/-- If `x ∈ closure s` and `y ∈ interior s`, then the segment `(x, y]` is included in `interior s`.
-/
theorem Convex.add_smul_sub_mem_interior' {s : Set E} (hs : Convex 𝕜 s) {x y : E}
    (hx : x ∈ closure s) (hy : y ∈ interior s) {t : 𝕜} (ht : t ∈ Ioc (0 : 𝕜) 1) :
    x + t • (y - x) ∈ interior s := by
  simpa only [sub_smul, smul_sub, one_smul, add_sub, add_comm] using
    hs.combo_interior_closure_mem_interior hy hx ht.1 (sub_nonneg.mpr ht.2)
      (add_sub_cancel _ _)

/-- If `x ∈ s` and `y ∈ interior s`, then the segment `(x, y]` is included in `interior s`. -/
theorem Convex.add_smul_sub_mem_interior {s : Set E} (hs : Convex 𝕜 s) {x y : E} (hx : x ∈ s)
    (hy : y ∈ interior s) {t : 𝕜} (ht : t ∈ Ioc (0 : 𝕜) 1) : x + t • (y - x) ∈ interior s :=
  hs.add_smul_sub_mem_interior' (subset_closure hx) hy ht

/-- If `x ∈ closure s` and `x + y ∈ interior s`, then `x + t y ∈ interior s` for `t ∈ (0, 1]`. -/
theorem Convex.add_smul_mem_interior' {s : Set E} (hs : Convex 𝕜 s) {x y : E} (hx : x ∈ closure s)
    (hy : x + y ∈ interior s) {t : 𝕜} (ht : t ∈ Ioc (0 : 𝕜) 1) : x + t • y ∈ interior s := by
  simpa only [add_sub_cancel_left] using hs.add_smul_sub_mem_interior' hx hy ht

/-- If `x ∈ s` and `x + y ∈ interior s`, then `x + t y ∈ interior s` for `t ∈ (0, 1]`. -/
theorem Convex.add_smul_mem_interior {s : Set E} (hs : Convex 𝕜 s) {x y : E} (hx : x ∈ s)
    (hy : x + y ∈ interior s) {t : 𝕜} (ht : t ∈ Ioc (0 : 𝕜) 1) : x + t • y ∈ interior s :=
  hs.add_smul_mem_interior' (subset_closure hx) hy ht

/-- In a topological vector space, the interior of a convex set is convex. -/
protected theorem Convex.interior {s : Set E} (hs : Convex 𝕜 s) : Convex 𝕜 (interior s) :=
  convex_iff_openSegment_subset.mpr fun _ hx _ hy =>
    hs.openSegment_closure_interior_subset_interior (interior_subset_closure hx) hy

/-- In a topological vector space, the closure of a convex set is convex. -/
protected theorem Convex.closure {s : Set E} (hs : Convex 𝕜 s) : Convex 𝕜 (closure s) :=
  fun x hx y hy a b ha hb hab =>
  let f : E → E → E := fun x' y' => a • x' + b • y'
  have hf : Continuous (Function.uncurry f) :=
    (continuous_fst.const_smul _).add (continuous_snd.const_smul _)
  show f x y ∈ closure s from map_mem_closure₂ hf hx hy fun _ hx' _ hy' => hs hx' hy' ha hb hab

open AffineMap

/-- A convex set `s` is strictly convex provided that for any two distinct points of
`s \ interior s`, the line passing through these points has nonempty intersection with
`interior s`. -/
protected theorem Convex.strictConvex' {s : Set E} (hs : Convex 𝕜 s)
    (h : (s \ interior s).Pairwise fun x y => ∃ c : 𝕜, lineMap x y c ∈ interior s) :
    StrictConvex 𝕜 s := by
  refine strictConvex_iff_openSegment_subset.2 ?_
  intro x hx y hy hne
  by_cases hx' : x ∈ interior s
  · exact hs.openSegment_interior_self_subset_interior hx' hy
  by_cases hy' : y ∈ interior s
  · exact hs.openSegment_self_interior_subset_interior hx hy'
  rcases h ⟨hx, hx'⟩ ⟨hy, hy'⟩ hne with ⟨c, hc⟩
  refine (openSegment_subset_union x y ⟨c, rfl⟩).trans
    (insert_subset_iff.2 ⟨hc, union_subset ?_ ?_⟩)
  exacts [hs.openSegment_self_interior_subset_interior hx hc,
    hs.openSegment_interior_self_subset_interior hc hy]

/-- A convex set `s` is strictly convex provided that for any two distinct points `x`, `y` of
`s \ interior s`, the segment with endpoints `x`, `y` has nonempty intersection with
`interior s`. -/
protected theorem Convex.strictConvex {s : Set E} (hs : Convex 𝕜 s)
    (h : (s \ interior s).Pairwise fun x y => ([x -[𝕜] y] \ frontier s).Nonempty) :
    StrictConvex 𝕜 s := by
  refine hs.strictConvex' <| h.imp_on fun x hx y hy _ => ?_
  simp only [segment_eq_image_lineMap, ← self_diff_frontier]
  rintro ⟨_, ⟨⟨c, hc, rfl⟩, hcs⟩⟩
  refine ⟨c, hs.segment_subset hx.1 hy.1 ?_, hcs⟩
  exact (segment_eq_image_lineMap 𝕜 x y).symm ▸ mem_image_of_mem _ hc

end ContinuousConstSMul

section ContinuousSMul

variable [LinearOrderedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [TopologicalSpace 𝕜] [OrderTopology 𝕜] [ContinuousSMul 𝕜 E]

theorem Convex.closure_interior_eq_closure_of_nonempty_interior {s : Set E} (hs : Convex 𝕜 s)
    (hs' : (interior s).Nonempty) : closure (interior s) = closure s :=
  subset_antisymm (closure_mono interior_subset)
    fun _ h ↦ closure_mono (hs.openSegment_interior_closure_subset_interior hs'.choose_spec h)
      (segment_subset_closure_openSegment (right_mem_segment ..))

theorem Convex.interior_closure_eq_interior_of_nonempty_interior {s : Set E} (hs : Convex 𝕜 s)
    (hs' : (interior s).Nonempty) : interior (closure s) = interior s := by
  refine subset_antisymm ?_ (interior_mono subset_closure)
  intro y hy
  rcases hs' with ⟨x, hx⟩
  have h := AffineMap.lineMap_apply_one (k := 𝕜) x y
  obtain ⟨t, ht1, ht⟩ := AffineMap.lineMap_continuous.tendsto' _ _ h |>.eventually_mem
    (mem_interior_iff_mem_nhds.1 hy) |>.exists_gt
  apply hs.openSegment_interior_closure_subset_interior hx ht
  nth_rw 1 [← AffineMap.lineMap_apply_zero (k := 𝕜) x y, ← image_openSegment]
  exact ⟨1, Ioo_subset_openSegment ⟨zero_lt_one, ht1⟩, h⟩

end ContinuousSMul

section TopologicalSpace

variable [OrderedSemiring 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]

theorem convex_closed_sInter {S : Set (Set E)} (h : ∀ s ∈ S, Convex 𝕜 s ∧ IsClosed s) :
    Convex 𝕜 (⋂₀ S) ∧ IsClosed (⋂₀ S) :=
  ⟨fun _ hx => starConvex_sInter fun _ hs => (h _ hs).1 <| hx _ hs,
    isClosed_sInter fun _ hs => (h _ hs).2⟩

variable (𝕜)

/-- The convex closed hull of a set `s` is the minimal convex closed set that includes `s`. -/
@[simps! isClosed]
def closedConvexHull : ClosureOperator (Set E) := .ofCompletePred (fun s => Convex 𝕜 s ∧ IsClosed s)
  fun _ ↦ convex_closed_sInter

variable {𝕜}

theorem convex_closedConvexHull {s : Set E} :
    Convex 𝕜 (closedConvexHull 𝕜 s) := ((closedConvexHull 𝕜).isClosed_closure s).1

theorem isClosed_closedConvexHull {s : Set E} :
    IsClosed (closedConvexHull 𝕜 s) := ((closedConvexHull 𝕜).isClosed_closure s).2

theorem subset_closedConvexHull {s : Set E} : s ⊆ closedConvexHull 𝕜 s :=
  (closedConvexHull 𝕜).le_closure s

theorem closure_subset_closedConvexHull {s : Set E} : closure s ⊆ closedConvexHull 𝕜 s :=
  closure_minimal subset_closedConvexHull isClosed_closedConvexHull

theorem closedConvexHull_min {s t : Set E} (hst : s ⊆ t) (h_conv : Convex 𝕜 t)
    (h_closed : IsClosed t) : closedConvexHull 𝕜 s ⊆ t :=
  (closedConvexHull 𝕜).closure_min hst ⟨h_conv, h_closed⟩

theorem convexHull_subset_closedConvexHull {s : Set E} :
    (convexHull 𝕜) s ⊆ (closedConvexHull 𝕜) s :=
  convexHull_min subset_closedConvexHull convex_closedConvexHull

@[simp]
theorem closedConvexHull_closure_eq_closedConvexHull {s : Set E} :
    closedConvexHull 𝕜 (closure s) = closedConvexHull 𝕜 s :=
  subset_antisymm (by
    simpa using ((closedConvexHull 𝕜).monotone (closure_subset_closedConvexHull (𝕜 := 𝕜) (E := E))))
    ((closedConvexHull 𝕜).monotone subset_closure)

end TopologicalSpace

section ContinuousConstSMul

variable [LinearOrderedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousConstSMul 𝕜 E]

theorem closedConvexHull_eq_closure_convexHull {s : Set E} :
    closedConvexHull 𝕜 s = closure (convexHull 𝕜 s) := subset_antisymm
  (closedConvexHull_min (subset_trans (subset_convexHull 𝕜 s) subset_closure)
    (Convex.closure (convex_convexHull 𝕜 s)) isClosed_closure)
  (closure_minimal convexHull_subset_closedConvexHull isClosed_closedConvexHull)

end ContinuousConstSMul

section ContinuousSMul

variable [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E]

/-- Convex hull of a finite set is compact. -/
theorem Set.Finite.isCompact_convexHull {s : Set E} (hs : s.Finite) :
    IsCompact (convexHull ℝ s) := by
  rw [hs.convexHull_eq_image]
  apply (@isCompact_stdSimplex _ hs.fintype).image
  haveI := hs.fintype
  apply LinearMap.continuous_on_pi

/-- Convex hull of a finite set is closed. -/
theorem Set.Finite.isClosed_convexHull [T2Space E] {s : Set E} (hs : s.Finite) :
    IsClosed (convexHull ℝ s) :=
  hs.isCompact_convexHull.isClosed

open AffineMap

/-- If we dilate the interior of a convex set about a point in its interior by a scale `t > 1`,
the result includes the closure of the original set.

TODO Generalise this from convex sets to sets that are balanced / star-shaped about `x`. -/
theorem Convex.closure_subset_image_homothety_interior_of_one_lt {s : Set E} (hs : Convex ℝ s)
    {x : E} (hx : x ∈ interior s) (t : ℝ) (ht : 1 < t) :
    closure s ⊆ homothety x t '' interior s := by
  intro y hy
  have hne : t ≠ 0 := (one_pos.trans ht).ne'
  refine
    ⟨homothety x t⁻¹ y, hs.openSegment_interior_closure_subset_interior hx hy ?_,
      (AffineEquiv.homothetyUnitsMulHom x (Units.mk0 t hne)).apply_symm_apply y⟩
  rw [openSegment_eq_image_lineMap, ← inv_one, ← inv_Ioi₀ (zero_lt_one' ℝ), ← image_inv_eq_inv,
    image_image, homothety_eq_lineMap]
  exact mem_image_of_mem _ ht

/-- If we dilate a convex set about a point in its interior by a scale `t > 1`, the interior of
the result includes the closure of the original set.

TODO Generalise this from convex sets to sets that are balanced / star-shaped about `x`. -/
theorem Convex.closure_subset_interior_image_homothety_of_one_lt {s : Set E} (hs : Convex ℝ s)
    {x : E} (hx : x ∈ interior s) (t : ℝ) (ht : 1 < t) :
    closure s ⊆ interior (homothety x t '' s) :=
  (hs.closure_subset_image_homothety_interior_of_one_lt hx t ht).trans <|
    (homothety_isOpenMap x t (one_pos.trans ht).ne').image_interior_subset _

/-- If we dilate a convex set about a point in its interior by a scale `t > 1`, the interior of
the result includes the closure of the original set.

TODO Generalise this from convex sets to sets that are balanced / star-shaped about `x`. -/
theorem Convex.subset_interior_image_homothety_of_one_lt {s : Set E} (hs : Convex ℝ s) {x : E}
    (hx : x ∈ interior s) (t : ℝ) (ht : 1 < t) : s ⊆ interior (homothety x t '' s) :=
  subset_closure.trans <| hs.closure_subset_interior_image_homothety_of_one_lt hx t ht

theorem JoinedIn.of_segment_subset {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul ℝ E]
    {x y : E} {s : Set E} (h : [x -[ℝ] y] ⊆ s) : JoinedIn s x y := by
  have A : Continuous (fun t ↦ (1 - t) • x + t • y : ℝ → E) := by fun_prop
  apply JoinedIn.ofLine A.continuousOn (by simp) (by simp)
  convert h
  rw [segment_eq_image ℝ x y]

/-- A nonempty convex set is path connected. -/
protected theorem Convex.isPathConnected {s : Set E} (hconv : Convex ℝ s) (hne : s.Nonempty) :
    IsPathConnected s := by
  refine isPathConnected_iff.mpr ⟨hne, ?_⟩
  intro x x_in y y_in
  exact JoinedIn.of_segment_subset ((segment_subset_iff ℝ).2 (hconv x_in y_in))

/-- A nonempty convex set is connected. -/
protected theorem Convex.isConnected {s : Set E} (h : Convex ℝ s) (hne : s.Nonempty) :
    IsConnected s :=
  (h.isPathConnected hne).isConnected

/-- A convex set is preconnected. -/
protected theorem Convex.isPreconnected {s : Set E} (h : Convex ℝ s) : IsPreconnected s :=
  s.eq_empty_or_nonempty.elim (fun h => h.symm ▸ isPreconnected_empty) fun hne =>
    (h.isConnected hne).isPreconnected

/-- Every topological vector space over ℝ is path connected.

Not an instance, because it creates enormous TC subproblems (turn on `pp.all`).
-/
protected theorem IsTopologicalAddGroup.pathConnectedSpace : PathConnectedSpace E :=
  pathConnectedSpace_iff_univ.mpr <| convex_univ.isPathConnected ⟨(0 : E), trivial⟩

end ContinuousSMul

section ComplementsConnected

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]

local notation "π" => Submodule.linearProjOfIsCompl _ _

attribute [local instance 100] IsTopologicalAddGroup.pathConnectedSpace

/-- Given two complementary subspaces `p` and `q` in `E`, if the complement of `{0}`
is path connected in `p` then the complement of `q` is path connected in `E`. -/
theorem isPathConnected_compl_of_isPathConnected_compl_zero [ContinuousSMul ℝ E]
    {p q : Submodule ℝ E} (hpq : IsCompl p q) (hpc : IsPathConnected ({0}ᶜ : Set p)) :
    IsPathConnected (qᶜ : Set E) := by
  rw [isPathConnected_iff] at hpc ⊢
  constructor
  · rcases hpc.1 with ⟨a, ha⟩
    exact ⟨a, mt (Submodule.eq_zero_of_coe_mem_of_disjoint hpq.disjoint) ha⟩
  · intro x hx y hy
    have : π hpq x ≠ 0 ∧ π hpq y ≠ 0 := by
      constructor <;> intro h <;> rw [Submodule.linearProjOfIsCompl_apply_eq_zero_iff hpq] at h <;>
        [exact hx h; exact hy h]
    rcases hpc.2 (π hpq x) this.1 (π hpq y) this.2 with ⟨γ₁, hγ₁⟩
    let γ₂ := PathConnectedSpace.somePath (π hpq.symm x) (π hpq.symm y)
    let γ₁' : Path (_ : E) _ := γ₁.map continuous_subtype_val
    let γ₂' : Path (_ : E) _ := γ₂.map continuous_subtype_val
    refine ⟨(γ₁'.add γ₂').cast (Submodule.linear_proj_add_linearProjOfIsCompl_eq_self hpq x).symm
      (Submodule.linear_proj_add_linearProjOfIsCompl_eq_self hpq y).symm, fun t ↦ ?_⟩
    rw [Path.cast_coe, Path.add_apply]
    change γ₁ t + (γ₂ t : E) ∉ q
    rw [← Submodule.linearProjOfIsCompl_apply_eq_zero_iff hpq, LinearMap.map_add,
      Submodule.linearProjOfIsCompl_apply_right, add_zero,
      Submodule.linearProjOfIsCompl_apply_eq_zero_iff]
    exact mt (Submodule.eq_zero_of_coe_mem_of_disjoint hpq.disjoint) (hγ₁ t)

end ComplementsConnected

section LinearOrderedField

variable {𝕜 : Type*} [LinearOrderedField 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜]

open scoped Topology

open Filter

theorem Convex.nontrivial_iff_nonempty_interior {s : Set 𝕜} (hs : Convex 𝕜 s) :
    s.Nontrivial ↔ (interior s).Nonempty := by
  constructor
  · rintro ⟨x, hx, y, hy, h⟩
    have hs' := Nonempty.mono <| interior_mono <| hs.segment_subset hx hy
    rw [segment_eq_Icc', interior_Icc, nonempty_Ioo, inf_lt_sup] at hs'
    exact hs' h
  · rintro ⟨x, hx⟩
    rcases eq_singleton_or_nontrivial (interior_subset hx) with rfl | h
    · rw [interior_singleton] at hx
      exact hx.elim
    · exact h

theorem Convex.diff_singleton_eventually_mem_nhds {s : Set 𝕜} (hs : Convex 𝕜 s) (a : 𝕜) :
    ∀ᶠ x in 𝓝[s \ {a}] a, s \ {a} ∈ 𝓝 x := by
  by_cases has : a ∈ closure s
  swap
  · rw [diff_singleton_eq_self (not_mem_subset subset_closure has),
      not_mem_closure_iff_nhdsWithin_eq_bot.1 has]
    apply eventually_bot
  rcases Nonempty.of_closure ⟨a, has⟩ with ⟨a', ha'⟩
  rcases eq_singleton_or_nontrivial ha' with rfl | h
  · rw [closure_singleton, mem_singleton_iff] at has
    rw [has, diff_self, nhdsWithin_empty]
    apply eventually_bot
  replace h := hs.interior_closure_eq_interior_of_nonempty_interior <|
    hs.nontrivial_iff_nonempty_interior.1 h
  conv in 𝓝[s \ {a}] a => rw [diff_eq, ← Iio_union_Ioi, inter_union_distrib_left]
  rw [nhdsWithin_union, eventually_sup]
  constructor
  · rcases eq_empty_or_nonempty (s ∩ Iio a) with hs' | ⟨b, hbs, hba⟩
    · rw [hs', nhdsWithin_empty]
      apply eventually_bot
    have := interior_mono <| hs.closure.openSegment_subset (subset_closure hbs) has
    rw [openSegment_eq_Ioo hba, interior_Ioo, h] at this
    replace this := this.trans interior_subset
    apply eventually_of_mem (U := Ioo b a)
    · exact mem_nhdsWithin.2 ⟨Ioi b, isOpen_Ioi, hba, fun _ ⟨h₁, _, h₂⟩ ↦ ⟨h₁, h₂⟩⟩
    · intro x hx
      exact mem_nhds_iff.2 ⟨Ioo b a, subset_diff_singleton this right_not_mem_Ioo, isOpen_Ioo, hx⟩
  · rcases eq_empty_or_nonempty (s ∩ Ioi a) with hs' | ⟨b, hbs, hab⟩
    · rw [hs', nhdsWithin_empty]
      apply eventually_bot
    have := interior_mono <| hs.closure.openSegment_subset has (subset_closure hbs)
    rw [openSegment_eq_Ioo hab, interior_Ioo, h] at this
    replace this := this.trans interior_subset
    apply eventually_of_mem (U := Ioo a b)
    · exact mem_nhdsWithin.2 ⟨Iio b, isOpen_Iio, hab, fun _ ⟨h₁, _, h₂⟩ ↦ ⟨h₂, h₁⟩⟩
    · intro x hx
      exact mem_nhds_iff.2 ⟨Ioo a b, subset_diff_singleton this left_not_mem_Ioo, isOpen_Ioo, hx⟩

end LinearOrderedField
