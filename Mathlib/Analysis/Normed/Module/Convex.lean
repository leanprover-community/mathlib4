/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.Normed.Group.Pointwise
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Module.RCLike.Real

/-!
# Metric properties of convex sets in normed spaces

We prove the following facts:

* `convexOn_norm`, `convexOn_dist` : norm and distance to a fixed point is convex on any convex
  set;
* `convexOn_univ_norm`, `convexOn_univ_dist` : norm and distance to a fixed point is convex on
  the whole space;
* `convexHull_ediam`, `convexHull_diam` : convex hull of a set has the same (e)metric diameter
  as the original set;
* `isBounded_convexHull` : convex hull of a set is bounded if and only if the original set
  is bounded.
-/

@[expose] public section

-- TODO assert_not_exists Cardinal

variable {E : Type*}

open Metric Set

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

theorem convex_ball (a : E) (r : ℝ) : Convex ℝ (ball a r) := by
  simpa only [Metric.ball, sep_univ] using (convexOn_univ_dist a).convex_lt r

theorem convex_eball (a : E) (r : ENNReal) : Convex ℝ (eball a r) := by
  cases r with
  | top => simp [convex_univ]
  | coe r => simp [eball_coe, convex_ball]

theorem convex_closedBall (a : E) (r : ℝ) : Convex ℝ (Metric.closedBall a r) := by
  simpa only [Metric.closedBall, sep_univ] using (convexOn_univ_dist a).convex_le r

theorem convex_closedEBall (a : E) (r : ENNReal) : Convex ℝ (closedEBall a r) := by
  cases r with
  | top => simp [convex_univ]
  | coe r => simp [closedEBall_coe, convex_closedBall]

open Pointwise in
theorem convexHull_sphere_eq_closedBall {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [Nontrivial F] (x : F) {r : ℝ} (hr : 0 ≤ r) :
    convexHull ℝ (sphere x r) = closedBall x r := by
  suffices convexHull ℝ (sphere (0 : F) r) = closedBall 0 r by
    rw [← add_zero x, ← vadd_eq_add, ← vadd_sphere, convexHull_vadd,
      this, vadd_closedBall_zero, vadd_eq_add, add_zero]
  refine subset_antisymm (convexHull_min sphere_subset_closedBall (convex_closedBall 0 r))
    (fun x h ↦ mem_convexHull_iff.mpr fun U hU_sub hU ↦ ?_)
  have zero_mem : (0 : F) ∈ U := by
    have _ : Invertible (2 : ℝ) := by use 2⁻¹ <;> grind
    obtain ⟨z, hz⟩ := NormedSpace.sphere_nonempty (E := F).mpr hr
    rw [← midpoint_self_neg (R := ℝ) (x := z)]
    exact Convex.midpoint_mem hU (hU_sub hz) <| hU_sub (by simp_all)
  by_cases hr₀ : r = 0
  · simp_all
  by_cases x_zero : x = 0
  · rwa [x_zero]
  set z := (r * ‖x‖⁻¹) • x with hz_def
  have hr₁ : r⁻¹ * ‖x‖ ≤ 1 := by
    simp only [mem_closedBall, dist_zero_right] at h
    grw [h, inv_mul_le_one]
  have hz : z ∈ U := by
    apply hU_sub
    simp_all [norm_smul]
  have := StarConvex.smul_mem (hU.starConvex zero_mem) hz (by positivity) hr₁
  rwa [hz_def, ← smul_assoc, smul_eq_mul, ← mul_assoc, mul_comm, mul_comm r⁻¹, mul_assoc _ r⁻¹,
    inv_mul_cancel₀ hr₀, mul_one, inv_mul_cancel₀ (by simp_all), one_smul] at this

/-- Given a point `x` in the convex hull of `s` and a point `y`, there exists a point
of `s` at distance at least `dist x y` from `y`. -/
theorem convexHull_exists_dist_ge {s : Set E} {x : E} (hx : x ∈ convexHull ℝ s) (y : E) :
    ∃ x' ∈ s, dist x y ≤ dist x' y :=
  (convexOn_dist y (convex_convexHull ℝ _)).exists_ge_of_mem_convexHull (subset_convexHull ..) hx

theorem Convex.thickening (hs : Convex ℝ s) (δ : ℝ) : Convex ℝ (thickening δ s) := by
  rw [← add_ball_zero]
  exact hs.add (convex_ball 0 _)

theorem Convex.cthickening (hs : Convex ℝ s) (δ : ℝ) : Convex ℝ (cthickening δ s) := by
  obtain hδ | hδ := le_total 0 δ
  · rw [cthickening_eq_iInter_thickening hδ]
    exact convex_iInter₂ fun _ _ => hs.thickening _
  · rw [cthickening_of_nonpos hδ]
    exact hs.closure

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
theorem convexHull_ediam (s : Set E) : ediam (convexHull ℝ s) = ediam s := by
  refine (ediam_le fun x hx y hy => ?_).antisymm (ediam_mono <| subset_convexHull ℝ s)
  rcases convexHull_exists_dist_ge2 hx hy with ⟨x', hx', y', hy', H⟩
  rw [edist_dist]
  apply le_trans (ENNReal.ofReal_le_ofReal H)
  rw [← edist_dist]
  exact edist_le_ediam_of_mem hx' hy'

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

/-- The set of vectors in the same ray as `x` is connected. -/
theorem isConnected_setOf_sameRay (x : E) : IsConnected { y | SameRay ℝ x y } := by
  by_cases hx : x = 0; · simpa [hx] using isConnected_univ (α := E)
  simp_rw [← exists_nonneg_left_iff_sameRay hx]
  exact isConnected_Ici.image _ (by fun_prop)

/-- The set of nonzero vectors in the same ray as the nonzero vector `x` is connected. -/
theorem isConnected_setOf_sameRay_and_ne_zero {x : E} (hx : x ≠ 0) :
    IsConnected { y | SameRay ℝ x y ∧ y ≠ 0 } := by
  simp_rw [← exists_pos_left_iff_sameRay_and_ne_zero hx]
  exact isConnected_Ioi.image _ (by fun_prop)

lemma norm_sub_le_of_mem_segment {x y z : E} (hy : y ∈ segment ℝ x z) :
    ‖y - x‖ ≤ ‖z - x‖ := by
  rw [segment_eq_image'] at hy
  simp only [mem_image, mem_Icc] at hy
  obtain ⟨u, ⟨hu_nonneg, hu_le_one⟩, rfl⟩ := hy
  simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
  rw [abs_of_nonneg hu_nonneg]
  conv_rhs => rw [← one_mul (‖z - x‖)]
  gcongr

namespace Filter

open scoped Convex Topology
variable {α : Type*} {f : Filter α} {x : E} {y z : α → E} {r : α → E → Prop}

theorem Eventually.segment_of_prod_nhds (hy : Tendsto y f (𝓝 x)) (hz : Tendsto z f (𝓝 x))
    (hr : ∀ᶠ p in f ×ˢ 𝓝 x, r p.1 p.2) : ∀ᶠ χ in f, ∀ v ∈ [y χ -[ℝ] z χ], r χ v := by
  obtain ⟨p, hp, δ, hδ, hr⟩ := eventually_prod_nhds_iff.mp hr
  rw [Metric.tendsto_nhds] at hy hz
  filter_upwards [hp, hy δ hδ, hz δ hδ] with χ hp hy hz
  exact fun v hv => hr hp <| convex_iff_segment_subset.mp (convex_ball x δ) hy hz hv

theorem Eventually.segment_of_prod_nhdsWithin (hy : Tendsto y f (𝓝 x)) (hz : Tendsto z f (𝓝 x))
    (hr : ∀ᶠ p in f ×ˢ 𝓝[s] x, r p.1 p.2) (seg : ∀ᶠ χ in f, [y χ -[ℝ] z χ] ⊆ s) :
    ∀ᶠ χ in f, ∀ v ∈ [y χ -[ℝ] z χ], r χ v := by
  refine seg.mp <| .mono ?_ (fun _ => forall₂_imp)
  apply Eventually.segment_of_prod_nhds hy hz
  simpa [nhdsWithin, prod_eq_inf, ← inf_assoc, eventually_inf_principal] using hr

end Filter

end SeminormedAddCommGroup
