/-
Copyright (c) 2024 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Topology.MetricSpace.Ultra.Basic

/-!
## Ultrametric norms

This file describes behavior of norms in ultrametric spaces.

## Main results

* A normed additive group has an ultrametric iff the norm is nonarchimedean

## Tags

ultrametric, nonarchimedean
-/
open Metric IsUltrametricDist

namespace IsUltrametricDist

lemma norm_add_le_max {X : Type*} [SeminormedAddGroup X] [IsUltrametricDist X] (x y : X) :
    ‖x + y‖ ≤ max ‖x‖ ‖y‖ := by
  simpa [dist_eq_norm x (-y)] using dist_triangle_max x 0 (-y)

lemma isUltrametricDist_of_forall_norm_add_le_max_norm {X : Type*} [SeminormedAddGroup X]
    (h : ∀ x y : X, ‖x + y‖ ≤ max ‖x‖ ‖y‖) : IsUltrametricDist X := by
  constructor
  intro x y z
  simp_rw [dist_eq_norm]
  apply (h _ _).trans'
  simp

lemma isUltrametricDist_of_isNonarchimedean_norm {X : Type*} [SeminormedAddGroup X]
    (h : IsNonarchimedean (norm : X → ℝ)) : IsUltrametricDist X :=
  isUltrametricDist_of_forall_norm_add_le_max_norm h

section AddGroup

variable {X : Type*} [SeminormedAddCommGroup X] [IsUltrametricDist X]

/-- All triangles are isosceles in an ultrametric normed commutative additive group. -/
lemma norm_add_eq_max_of_norm_ne_norm
    {x y : X} (h : ‖x‖ ≠ ‖y‖) : ‖x + y‖ = max ‖x‖ ‖y‖ := by
  wlog hxy : ‖y‖ ≤ ‖x‖
  · rw [add_comm, max_comm]
    exact this (Ne.symm h) (le_of_not_le hxy)
  · rw [max_eq_left hxy]
    refine le_antisymm ((norm_add_le_max x y).trans ?_) ?_
    · simp [h, hxy]
    · simpa [(lt_of_le_of_ne hxy (Ne.symm h)).not_le] using norm_add_le_max (x + y) (-y)

/-- All triangles are isosceles in an ultrametric normed commutative additive group. -/
lemma norm_sub_eq_max_of_norm_sub_ne_norm_sub (x y z : X) (h : ‖x - y‖ ≠ ‖y - z‖) :
    ‖x - z‖ = max ‖x - y‖ ‖y - z‖ := by
  simpa using norm_add_eq_max_of_norm_ne_norm h

/-- All triangles are isosceles in an ultrametric normed commutative additive group. -/
lemma dist_eq_max_of_dist_ne_dist (x y z : X) (h : dist x y ≠ dist y z) :
    dist x z = max (dist x y) (dist y z) := by
  simp only [dist_eq_norm] at h ⊢
  exact norm_sub_eq_max_of_norm_sub_ne_norm_sub _ _ _ h

end AddGroup

section Field

variable {K : Type*} [NormedField K]

lemma norm_add_one_le_max_norm_one [IsUltrametricDist K] (x : K) :
    ‖x + 1‖ ≤ max ‖x‖ 1 := by
  simpa using norm_add_le_max x 1

lemma norm_sub_one_le_one_of_norm_le_one [IsUltrametricDist K] {x : K} (h : ‖x‖ ≤ 1) :
    ‖x - 1‖ ≤ 1 := by
  simpa [←sub_eq_add_neg, h] using norm_add_le_max x (-1)

lemma isUltrametricDist_of_forall_norm_add_one_le_max_norm_one
    (h : ∀ x : K, ‖x + 1‖ ≤ max ‖x‖ 1) : IsUltrametricDist K := by
  apply isUltrametricDist_of_forall_norm_add_le_max_norm
  intro x y
  rcases eq_or_ne y 0 with rfl|hy
  · simp
  rw [← div_le_div_right (c := ‖y‖) (by simpa using hy), ← norm_div, add_div, div_self hy,
      ← max_div_div_right (norm_nonneg _), div_self (by simp [hy]), ← norm_div]
  exact h _

lemma isUltrametricDist_of_forall_norm_sub_one_of_norm_le_one
    (h : ∀ x : K, ‖x‖ ≤ 1 → ‖x - 1‖ ≤ 1) : IsUltrametricDist K := by
  have : ∀ x : K, ‖x‖ ≤ 1 → ‖x + 1‖ ≤ 1 := by
    intro x hx
    specialize h (-x) (by simpa using hx)
    rwa [← neg_add', norm_neg] at h
  apply isUltrametricDist_of_forall_norm_add_one_le_max_norm_one
  intro x
  cases le_or_lt ‖x‖ 1 with
  | inl h => simpa [h] using this _ h
  | inr h =>
    suffices ‖x + 1‖ ≤ ‖x‖ by simp [this]
    rw [← div_le_div_right (c := ‖x‖) (h.trans' zero_lt_one), div_self (h.trans' zero_lt_one).ne',
        ← norm_div, add_div, div_self (by simpa using (h.trans' zero_lt_one)), add_comm]
    apply this
    simp [inv_le_one_iff, h.le]

end Field

end IsUltrametricDist
