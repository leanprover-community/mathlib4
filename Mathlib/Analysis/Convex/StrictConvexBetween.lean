/-
Copyright (c) 2022 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.Analysis.Convex.Between
public import Mathlib.Analysis.Convex.StrictConvexSpace
public import Mathlib.Analysis.Normed.Affine.AddTorsor
public import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Algebra.Order.Monoid.NatCast
import Mathlib.Algebra.Ring.CharZero
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Betweenness in affine spaces for strictly convex spaces

This file proves results about betweenness for points in an affine space for a strictly convex
space.

-/

@[expose] public section

open Metric
open scoped Convex

variable {V P : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [StrictConvexSpace ℝ V]

section PseudoMetricSpace
variable [PseudoMetricSpace P] [NormedAddTorsor V P]

theorem Sbtw.dist_lt_max_dist (p : P) {p₁ p₂ p₃ : P} (h : Sbtw ℝ p₁ p₂ p₃) :
    dist p₂ p < max (dist p₁ p) (dist p₃ p) := by
  have hp₁p₃ : p₁ -ᵥ p ≠ p₃ -ᵥ p := by simpa using h.left_ne_right
  rw [Sbtw, ← wbtw_vsub_const_iff p, Wbtw, affineSegment_eq_segment, ← insert_endpoints_openSegment,
    Set.mem_insert_iff, Set.mem_insert_iff] at h
  rcases h with ⟨h | h | h, hp₂p₁, hp₂p₃⟩
  · rw [vsub_left_cancel_iff] at h
    exact False.elim (hp₂p₁ h)
  · rw [vsub_left_cancel_iff] at h
    exact False.elim (hp₂p₃ h)
  · rw [openSegment_eq_image, Set.mem_image] at h
    rcases h with ⟨r, ⟨hr0, hr1⟩, hr⟩
    simp_rw [@dist_eq_norm_vsub V, ← hr]
    exact
      norm_combo_lt_of_ne (le_max_left _ _) (le_max_right _ _) hp₁p₃ (sub_pos.2 hr1) hr0 (by abel)

theorem Wbtw.dist_le_max_dist (p : P) {p₁ p₂ p₃ : P} (h : Wbtw ℝ p₁ p₂ p₃) :
    dist p₂ p ≤ max (dist p₁ p) (dist p₃ p) := by
  by_cases hp₁ : p₂ = p₁; · simp [hp₁]
  by_cases hp₃ : p₂ = p₃; · simp [hp₃]
  have hs : Sbtw ℝ p₁ p₂ p₃ := ⟨h, hp₁, hp₃⟩
  exact (hs.dist_lt_max_dist _).le

/-- Given three collinear points, two (not equal) with distance `r` from `p` and one with
distance at most `r` from `p`, the third point is weakly between the other two points. -/
theorem Collinear.wbtw_of_dist_eq_of_dist_le {p p₁ p₂ p₃ : P} {r : ℝ}
    (h : Collinear ℝ ({p₁, p₂, p₃} : Set P)) (hp₁ : dist p₁ p = r) (hp₂ : dist p₂ p ≤ r)
    (hp₃ : dist p₃ p = r) (hp₁p₃ : p₁ ≠ p₃) : Wbtw ℝ p₁ p₂ p₃ := by
  rcases h.wbtw_or_wbtw_or_wbtw with (hw | hw | hw)
  · exact hw
  · by_cases hp₃p₂ : p₃ = p₂
    · simp [hp₃p₂]
    have hs : Sbtw ℝ p₂ p₃ p₁ := ⟨hw, hp₃p₂, hp₁p₃.symm⟩
    have hs' := hs.dist_lt_max_dist p
    rw [hp₁, hp₃, lt_max_iff, lt_self_iff_false, or_false] at hs'
    exact False.elim (hp₂.not_gt hs')
  · by_cases hp₁p₂ : p₁ = p₂
    · simp [hp₁p₂]
    have hs : Sbtw ℝ p₃ p₁ p₂ := ⟨hw, hp₁p₃, hp₁p₂⟩
    have hs' := hs.dist_lt_max_dist p
    rw [hp₁, hp₃, lt_max_iff, lt_self_iff_false, false_or] at hs'
    exact False.elim (hp₂.not_gt hs')

/-- Given three collinear points, two (not equal) with distance `r` from `p` and one with
distance less than `r` from `p`, the third point is strictly between the other two points. -/
theorem Collinear.sbtw_of_dist_eq_of_dist_lt {p p₁ p₂ p₃ : P} {r : ℝ}
    (h : Collinear ℝ ({p₁, p₂, p₃} : Set P)) (hp₁ : dist p₁ p = r) (hp₂ : dist p₂ p < r)
    (hp₃ : dist p₃ p = r) (hp₁p₃ : p₁ ≠ p₃) : Sbtw ℝ p₁ p₂ p₃ := by
  refine ⟨h.wbtw_of_dist_eq_of_dist_le hp₁ hp₂.le hp₃ hp₁p₃, ?_, ?_⟩
  · rintro rfl
    exact hp₂.ne hp₁
  · rintro rfl
    exact hp₂.ne hp₃

end PseudoMetricSpace

section MetricSpace
variable [MetricSpace P] [NormedAddTorsor V P] {a b c : P}

/-- In a strictly convex space, the triangle inequality turns into an equality if and only if the
middle point belongs to the segment joining two other points. -/
lemma dist_add_dist_eq_iff : dist a b + dist b c = dist a c ↔ Wbtw ℝ a b c := by
  have :
      dist (a -ᵥ a) (b -ᵥ a) + dist (b -ᵥ a) (c -ᵥ a) = dist (a -ᵥ a) (c -ᵥ a) ↔
        b -ᵥ a ∈ segment ℝ (a -ᵥ a) (c -ᵥ a) := by
    simp only [mem_segment_iff_sameRay, sameRay_iff_norm_add, dist_eq_norm', sub_add_sub_cancel',
      eq_comm]
  simp_rw [dist_vsub_cancel_right, ← affineSegment_eq_segment, ← affineSegment_vsub_const_image]
    at this
  rwa [(vsub_left_injective _).mem_set_image] at this

/-- The strict triangle inequality. -/
theorem dist_lt_dist_add_dist_iff {a b c : P} :
    dist a c < dist a b + dist b c ↔ ¬ Wbtw ℝ a b c := by
  rw [← ne_iff_lt_iff_le.mpr (dist_triangle _ _ _), not_iff_not, eq_comm, dist_add_dist_eq_iff]

end MetricSpace

variable {E F PE PF : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ E]
  [NormedSpace ℝ F] [StrictConvexSpace ℝ E] [MetricSpace PE] [MetricSpace PF] [NormedAddTorsor E PE]
  [NormedAddTorsor F PF] {r : ℝ} {f : PF → PE} {x y z : PE}

lemma eq_lineMap_of_dist_eq_mul_of_dist_eq_mul (hxy : dist x y = r * dist x z)
    (hyz : dist y z = (1 - r) * dist x z) : y = AffineMap.lineMap x z r := by
  have : y -ᵥ x ∈ [(0 : E) -[ℝ] z -ᵥ x] := by
    rw [mem_segment_iff_wbtw, ← dist_add_dist_eq_iff, dist_zero, dist_vsub_cancel_right,
      ← dist_eq_norm_vsub', ← dist_eq_norm_vsub', hxy, hyz, ← add_mul, add_sub_cancel,
      one_mul]
  obtain rfl | hne := eq_or_ne x z
  · obtain rfl : y = x := by simpa
    simp
  · rw [← dist_ne_zero] at hne
    obtain ⟨a, b, _, hb, _, H⟩ := this
    rw [smul_zero, zero_add] at H
    have H' := congr_arg norm H
    rw [norm_smul, Real.norm_of_nonneg hb, ← dist_eq_norm_vsub', ← dist_eq_norm_vsub', hxy,
      mul_left_inj' hne] at H'
    rw [AffineMap.lineMap_apply, ← H', H, vsub_vadd]

lemma eq_midpoint_of_dist_eq_half (hx : dist x y = dist x z / 2) (hy : dist y z = dist x z / 2) :
    y = midpoint ℝ x z := by
  apply eq_lineMap_of_dist_eq_mul_of_dist_eq_mul
  · rwa [invOf_eq_inv, ← div_eq_inv_mul]
  · rwa [invOf_eq_inv, ← one_div, sub_half, one_div, ← div_eq_inv_mul]

namespace Isometry

/-- An isometry of `NormedAddTorsor`s for real normed spaces, strictly convex in the case of the
codomain, is an affine isometry.  Unlike Mazur-Ulam, this does not require the isometry to be
surjective. -/
noncomputable def affineIsometryOfStrictConvexSpace (hi : Isometry f) : PF →ᵃⁱ[ℝ] PE :=
  { AffineMap.ofMapMidpoint f
      (fun x y => by
        apply eq_midpoint_of_dist_eq_half
        · rw [hi.dist_eq, hi.dist_eq]
          simp only [dist_left_midpoint, Real.norm_of_nonneg zero_le_two, div_eq_inv_mul]
        · rw [hi.dist_eq, hi.dist_eq]
          simp only [dist_midpoint_right, Real.norm_of_nonneg zero_le_two, div_eq_inv_mul])
      hi.continuous with
    norm_map := fun x => by simp [AffineMap.ofMapMidpoint, ← dist_eq_norm_vsub E, hi.dist_eq] }

@[simp] lemma coe_affineIsometryOfStrictConvexSpace (hi : Isometry f) :
    ⇑hi.affineIsometryOfStrictConvexSpace = f := rfl

@[simp] lemma affineIsometryOfStrictConvexSpace_apply (hi : Isometry f) (p : PF) :
    hi.affineIsometryOfStrictConvexSpace p = f p := rfl

end Isometry
