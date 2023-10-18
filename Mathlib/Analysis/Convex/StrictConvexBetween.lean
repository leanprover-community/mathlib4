/-
Copyright (c) 2022 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib.Analysis.Convex.Between
import Mathlib.Analysis.Convex.StrictConvexSpace

#align_import analysis.convex.strict_convex_between from "leanprover-community/mathlib"@"e1730698f86560a342271c0471e4cb72d021aabf"

/-!
# Betweenness in affine spaces for strictly convex spaces

This file proves results about betweenness for points in an affine space for a strictly convex
space.

-/

open Metric

variable {V P : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

section to_move
variable [PseudoMetricSpace P] [NormedAddTorsor V P]

-- TODO: Is there a better place for this lemma?
lemma Wbtw.dist_add_dist {x y z : P} (h : Wbtw ℝ x y z) : dist x y + dist y z = dist x z := by
  obtain ⟨a, ⟨ha₀, ha₁⟩, rfl⟩ := h; simp [abs_of_nonneg, ha₀, ha₁, sub_mul]

end to_move

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
#align sbtw.dist_lt_max_dist Sbtw.dist_lt_max_dist

theorem Wbtw.dist_le_max_dist (p : P) {p₁ p₂ p₃ : P} (h : Wbtw ℝ p₁ p₂ p₃) :
    dist p₂ p ≤ max (dist p₁ p) (dist p₃ p) := by
  by_cases hp₁ : p₂ = p₁; · simp [hp₁]
  by_cases hp₃ : p₂ = p₃; · simp [hp₃]
  have hs : Sbtw ℝ p₁ p₂ p₃ := ⟨h, hp₁, hp₃⟩
  exact (hs.dist_lt_max_dist _).le
#align wbtw.dist_le_max_dist Wbtw.dist_le_max_dist

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
    rw [hp₁, hp₃, lt_max_iff, lt_self_iff_false, or_false_iff] at hs'
    exact False.elim (hp₂.not_lt hs')
  · by_cases hp₁p₂ : p₁ = p₂
    · simp [hp₁p₂]
    have hs : Sbtw ℝ p₃ p₁ p₂ := ⟨hw, hp₁p₃, hp₁p₂⟩
    have hs' := hs.dist_lt_max_dist p
    rw [hp₁, hp₃, lt_max_iff, lt_self_iff_false, false_or_iff] at hs'
    exact False.elim (hp₂.not_lt hs')
#align collinear.wbtw_of_dist_eq_of_dist_le Collinear.wbtw_of_dist_eq_of_dist_le

/-- Given three collinear points, two (not equal) with distance `r` from `p` and one with
distance less than `r` from `p`, the third point is strictly between the other two points. -/
theorem Collinear.sbtw_of_dist_eq_of_dist_lt {p p₁ p₂ p₃ : P} {r : ℝ}
    (h : Collinear ℝ ({p₁, p₂, p₃} : Set P)) (hp₁ : dist p₁ p = r) (hp₂ : dist p₂ p < r)
    (hp₃ : dist p₃ p = r) (hp₁p₃ : p₁ ≠ p₃) : Sbtw ℝ p₁ p₂ p₃ := by
  refine' ⟨h.wbtw_of_dist_eq_of_dist_le hp₁ hp₂.le hp₃ hp₁p₃, _, _⟩
  · rintro rfl
    exact hp₂.ne hp₁
  · rintro rfl
    exact hp₂.ne hp₃
#align collinear.sbtw_of_dist_eq_of_dist_lt Collinear.sbtw_of_dist_eq_of_dist_lt

end PseudoMetricSpace

section MetricSpace
variable [MetricSpace P] [NormedAddTorsor V P] {a b c : P}

/-- If the triangle `abc` is flat (the triangle inequality is an equality), then `b` lies between
`a` and `c`.

TODO: Deduplicate from `dist_add_dist_eq_iff`. -/
lemma dist_add_dist_eq_iff_wbtw : dist a b + dist b c = dist a c ↔ Wbtw ℝ a b c := by
  obtain rfl | hac := eq_or_ne a c
  · simp [dist_comm, eq_comm]
  refine ⟨fun habc ↦ ?_, Wbtw.dist_add_dist⟩
  refine ⟨dist a b / dist a c, ⟨by positivity, div_le_one_of_le ?_ <| by positivity⟩, Eq.symm <|
    eq_lineMap_of_dist_eq_mul_of_dist_eq_mul (div_mul_cancel _ <| dist_ne_zero.2 hac).symm ?_⟩
  · rw [←habc]
    exact le_add_of_nonneg_right <| by positivity
  · rwa [one_sub_mul, div_mul_cancel _ <| dist_ne_zero.2 hac, eq_sub_iff_add_eq']

end MetricSpace
