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


variable {V P : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [PseudoMetricSpace P]

variable [NormedAddTorsor V P] [StrictConvexSpace ℝ V]

theorem Sbtw.dist_lt_max_dist (p : P) {p₁ p₂ p₃ : P} (h : Sbtw ℝ p₁ p₂ p₃) :
    dist p₂ p < max (dist p₁ p) (dist p₃ p) := by
  have hp₁p₃ : p₁ -ᵥ p ≠ p₃ -ᵥ p := by simpa using h.left_ne_right
  -- ⊢ dist p₂ p < max (dist p₁ p) (dist p₃ p)
  rw [Sbtw, ← wbtw_vsub_const_iff p, Wbtw, affineSegment_eq_segment, ← insert_endpoints_openSegment,
    Set.mem_insert_iff, Set.mem_insert_iff] at h
  rcases h with ⟨h | h | h, hp₂p₁, hp₂p₃⟩
  · rw [vsub_left_cancel_iff] at h
    -- ⊢ dist p₂ p < max (dist p₁ p) (dist p₃ p)
    exact False.elim (hp₂p₁ h)
    -- 🎉 no goals
  · rw [vsub_left_cancel_iff] at h
    -- ⊢ dist p₂ p < max (dist p₁ p) (dist p₃ p)
    exact False.elim (hp₂p₃ h)
    -- 🎉 no goals
  · rw [openSegment_eq_image, Set.mem_image] at h
    -- ⊢ dist p₂ p < max (dist p₁ p) (dist p₃ p)
    rcases h with ⟨r, ⟨hr0, hr1⟩, hr⟩
    -- ⊢ dist p₂ p < max (dist p₁ p) (dist p₃ p)
    simp_rw [@dist_eq_norm_vsub V, ← hr]
    -- ⊢ ‖(1 - r) • (p₁ -ᵥ p) + r • (p₃ -ᵥ p)‖ < max ‖p₁ -ᵥ p‖ ‖p₃ -ᵥ p‖
    exact
      norm_combo_lt_of_ne (le_max_left _ _) (le_max_right _ _) hp₁p₃ (sub_pos.2 hr1) hr0 (by abel)
#align sbtw.dist_lt_max_dist Sbtw.dist_lt_max_dist

theorem Wbtw.dist_le_max_dist (p : P) {p₁ p₂ p₃ : P} (h : Wbtw ℝ p₁ p₂ p₃) :
    dist p₂ p ≤ max (dist p₁ p) (dist p₃ p) := by
  by_cases hp₁ : p₂ = p₁; · simp [hp₁]
  -- ⊢ dist p₂ p ≤ max (dist p₁ p) (dist p₃ p)
                            -- 🎉 no goals
  by_cases hp₃ : p₂ = p₃; · simp [hp₃]
  -- ⊢ dist p₂ p ≤ max (dist p₁ p) (dist p₃ p)
                            -- 🎉 no goals
  have hs : Sbtw ℝ p₁ p₂ p₃ := ⟨h, hp₁, hp₃⟩
  -- ⊢ dist p₂ p ≤ max (dist p₁ p) (dist p₃ p)
  exact (hs.dist_lt_max_dist _).le
  -- 🎉 no goals
#align wbtw.dist_le_max_dist Wbtw.dist_le_max_dist

/-- Given three collinear points, two (not equal) with distance `r` from `p` and one with
distance at most `r` from `p`, the third point is weakly between the other two points. -/
theorem Collinear.wbtw_of_dist_eq_of_dist_le {p p₁ p₂ p₃ : P} {r : ℝ}
    (h : Collinear ℝ ({p₁, p₂, p₃} : Set P)) (hp₁ : dist p₁ p = r) (hp₂ : dist p₂ p ≤ r)
    (hp₃ : dist p₃ p = r) (hp₁p₃ : p₁ ≠ p₃) : Wbtw ℝ p₁ p₂ p₃ := by
  rcases h.wbtw_or_wbtw_or_wbtw with (hw | hw | hw)
  · exact hw
    -- 🎉 no goals
  · by_cases hp₃p₂ : p₃ = p₂
    -- ⊢ Wbtw ℝ p₁ p₂ p₃
    · simp [hp₃p₂]
      -- 🎉 no goals
    have hs : Sbtw ℝ p₂ p₃ p₁ := ⟨hw, hp₃p₂, hp₁p₃.symm⟩
    -- ⊢ Wbtw ℝ p₁ p₂ p₃
    have hs' := hs.dist_lt_max_dist p
    -- ⊢ Wbtw ℝ p₁ p₂ p₃
    rw [hp₁, hp₃, lt_max_iff, lt_self_iff_false, or_false_iff] at hs'
    -- ⊢ Wbtw ℝ p₁ p₂ p₃
    exact False.elim (hp₂.not_lt hs')
    -- 🎉 no goals
  · by_cases hp₁p₂ : p₁ = p₂
    -- ⊢ Wbtw ℝ p₁ p₂ p₃
    · simp [hp₁p₂]
      -- 🎉 no goals
    have hs : Sbtw ℝ p₃ p₁ p₂ := ⟨hw, hp₁p₃, hp₁p₂⟩
    -- ⊢ Wbtw ℝ p₁ p₂ p₃
    have hs' := hs.dist_lt_max_dist p
    -- ⊢ Wbtw ℝ p₁ p₂ p₃
    rw [hp₁, hp₃, lt_max_iff, lt_self_iff_false, false_or_iff] at hs'
    -- ⊢ Wbtw ℝ p₁ p₂ p₃
    exact False.elim (hp₂.not_lt hs')
    -- 🎉 no goals
#align collinear.wbtw_of_dist_eq_of_dist_le Collinear.wbtw_of_dist_eq_of_dist_le

/-- Given three collinear points, two (not equal) with distance `r` from `p` and one with
distance less than `r` from `p`, the third point is strictly between the other two points. -/
theorem Collinear.sbtw_of_dist_eq_of_dist_lt {p p₁ p₂ p₃ : P} {r : ℝ}
    (h : Collinear ℝ ({p₁, p₂, p₃} : Set P)) (hp₁ : dist p₁ p = r) (hp₂ : dist p₂ p < r)
    (hp₃ : dist p₃ p = r) (hp₁p₃ : p₁ ≠ p₃) : Sbtw ℝ p₁ p₂ p₃ := by
  refine' ⟨h.wbtw_of_dist_eq_of_dist_le hp₁ hp₂.le hp₃ hp₁p₃, _, _⟩
  -- ⊢ p₂ ≠ p₁
  · rintro rfl
    -- ⊢ False
    exact hp₂.ne hp₁
    -- 🎉 no goals
  · rintro rfl
    -- ⊢ False
    exact hp₂.ne hp₃
    -- 🎉 no goals
#align collinear.sbtw_of_dist_eq_of_dist_lt Collinear.sbtw_of_dist_eq_of_dist_lt
