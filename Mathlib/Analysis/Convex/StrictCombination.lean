/-
Copyright (c) 2025 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.Analysis.Convex.StrictConvexSpace
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.LinearAlgebra.AffineSpace.Simplex.Basic

/-!
# Convex combinations in strictly convex sets and spaces.

This file proves lemmas about convex combinations of points in strictly convex sets and strictly
convex spaces.

-/

public section


open Finset Metric

variable {R V P ι : Type*}

section Set

variable [Field R] [LinearOrder R] [IsStrictOrderedRing R] [TopologicalSpace V] [AddCommGroup V]
variable [Module R V]

lemma StrictConvex.centerMass_mem_interior {s : Set V} {t : Finset ι} {w : ι → R} {z : ι → V}
    (hs : StrictConvex R s) :
    (∀ i ∈ t, 0 ≤ w i) → ∀ i j, i ∈ t → j ∈ t → z i ≠ z j → w i ≠ 0 → w j ≠ 0 →
      (∀ i ∈ t, z i ∈ s) → t.centerMass w z ∈ interior s := by
  classical
  induction t using Finset.induction with
  | empty => simp
  | insert i t hi ht =>
    intro h₀ i' j' hi' hj' hi'j' hi'0 hj'0 hmem
    have zi : z i ∈ s := hmem _ (mem_insert_self _ _)
    have hs₀ : ∀ j ∈ t, 0 ≤ w j := fun j hj => h₀ j <| mem_insert_of_mem hj
    by_cases hsum_t : ∑ j ∈ t, w j = 0
    · have ws : ∀ j ∈ t, w j = 0 := (sum_eq_zero_iff_of_nonneg hs₀).1 hsum_t
      have h : i' ∈ t ∨ j' ∈ t := by grind
      exfalso
      rcases h with h | h
      · exact hi'0 (ws _ h)
      · exact hj'0 (ws _ h)
    rw [Finset.centerMass_insert _ _ _ hi hsum_t]
    by_cases hi : w i = 0
    · simp only [hi, zero_add, zero_div, zero_smul, ne_eq, hsum_t, not_false_eq_true, div_self,
        one_smul]
      grind
    by_cases hzi : z i = t.centerMass w z
    · have hwi : w i + ∑ j ∈ t, w j ≠ 0 := by
        refine LT.lt.ne' ?_
        have hwi : 0 < w i := by grind
        grw [hwi]
        simp only [lt_add_iff_pos_right, gt_iff_lt]
        exact (sum_nonneg hs₀).lt_of_ne' hsum_t
      simp only [hzi, ← add_smul, ← add_div, ne_eq, hwi, not_false_eq_true, div_self, one_smul]
      by_cases! hijt : ∃ i'' j'', i'' ∈ t ∧ j'' ∈ t ∧ z i'' ≠ z j'' ∧ w i'' ≠ 0 ∧ w j'' ≠ 0
      · grind
      · exfalso
        obtain ⟨i'', hi'', hwi''⟩ : ∃ i'' ∈ t, w i'' ≠ 0 := by grind
        have hijt' : ∀ j'', j'' ∈ t → w j'' ≠ 0 → z j'' = Function.const _ (z i'') j'' := by
          grind
        have hi : i = i' ∨ i = j' := by grind
        have hzi'' : t.centerMass w z = z i'' := by
          rw [t.centerMass_congr_fun hijt', t.centerMass_const hsum_t]
        grind
    · exact strictConvex_iff_div.1 hs zi
        (hs.convex.centerMass_mem hs₀ (lt_of_le_of_ne (sum_nonneg hs₀) (Ne.symm hsum_t))
          (fun j hj ↦ hmem j (mem_insert_of_mem hj))) hzi (by grind)
        ((sum_nonneg hs₀).lt_of_ne' hsum_t)

lemma StrictConvex.sum_mem_interior {s : Set V} {t : Finset ι} {w : ι → R} {z : ι → V}
    (hs : StrictConvex R s) (h0 : ∀ i ∈ t, 0 ≤ w i) (h1 : ∑ i ∈ t, w i = 1) {i j : ι}
    (hi : i ∈ t) (hj : j ∈ t) (hij : z i ≠ z j) (hi0 : w i ≠ 0) (hj0 : w j ≠ 0)
    (hz : ∀ i ∈ t, z i ∈ s) : ∑ k ∈ t, w k • z k ∈ interior s := by
  rw [← t.centerMass_eq_of_sum_1 _ h1]
  exact hs.centerMass_mem_interior h0 i j hi hj hij hi0 hj0 hz

end Set

section Space

variable [NormedAddCommGroup V] [NormedSpace ℝ V] [StrictConvexSpace ℝ V]

lemma centerMass_mem_ball_of_strictConvexSpace {t : Finset ι} {w : ι → ℝ} {p : V} {r : ℝ}
    {z : ι → V} (h0 : ∀ i ∈ t, 0 ≤ w i) {i j : ι} (hi : i ∈ t) (hj : j ∈ t) (hij : z i ≠ z j)
    (hi0 : w i ≠ 0) (hj0 : w j ≠ 0) (hz : ∀ i ∈ t, z i ∈ closedBall p r) :
    t.centerMass w z ∈ ball p r := by
  rcases eq_or_ne r 0 with (rfl | hr)
  · simp_all
  · rw [← interior_closedBall _ hr]
    exact (strictConvex_closedBall _ _ _).centerMass_mem_interior h0 i j hi hj hij hi0 hj0 hz

lemma sum_mem_ball_of_strictConvexSpace {t : Finset ι} {w : ι → ℝ} {p : V} {r : ℝ} {z : ι → V}
    (h0 : ∀ i ∈ t, 0 ≤ w i) (h1 : ∑ i ∈ t, w i = 1) {i j : ι} (hi : i ∈ t) (hj : j ∈ t)
    (hij : z i ≠ z j) (hi0 : w i ≠ 0) (hj0 : w j ≠ 0) (hz : ∀ i ∈ t, z i ∈ closedBall p r) :
    ∑ k ∈ t, w k • z k ∈ ball p r := by
  rw [← t.centerMass_eq_of_sum_1 _ h1]
  exact centerMass_mem_ball_of_strictConvexSpace h0 hi hj hij hi0 hj0 hz

lemma norm_sum_lt_of_strictConvexSpace {t : Finset ι} {w : ι → ℝ} {r : ℝ} {z : ι → V}
    (h0 : ∀ i ∈ t, 0 ≤ w i) (h1 : ∑ i ∈ t, w i = 1) {i j : ι} (hi : i ∈ t) (hj : j ∈ t)
    (hij : z i ≠ z j) (hi0 : w i ≠ 0) (hj0 : w j ≠ 0) (hz : ∀ i ∈ t, ‖z i‖ ≤ r) :
    ‖∑ k ∈ t, w k • z k‖ < r := by
  simp_rw [← mem_closedBall_zero_iff] at hz
  rw [← mem_ball_zero_iff]
  exact sum_mem_ball_of_strictConvexSpace h0 h1 hi hj hij hi0 hj0 hz

variable [PseudoMetricSpace P] [NormedAddTorsor V P]

lemma dist_affineCombination_lt_of_strictConvexSpace {t : Finset ι} {w : ι → ℝ} {p₀ : P} {r : ℝ}
    {p : ι → P} (h0 : ∀ i ∈ t, 0 ≤ w i) (h1 : ∑ i ∈ t, w i = 1) {i j : ι} (hi : i ∈ t)
    (hj : j ∈ t) (hij : p i ≠ p j) (hi0 : w i ≠ 0) (hj0 : w j ≠ 0)
    (hp : ∀ i ∈ t, dist (p i) p₀ ≤ r) :
    dist (t.affineCombination ℝ p w) p₀ < r := by
  rw [affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one _ _ _ h1 p₀,
    weightedVSubOfPoint_apply, dist_vadd_left]
  simp_rw [dist_eq_norm_vsub] at hp
  exact norm_sum_lt_of_strictConvexSpace h0 h1 hi hj (by simpa using hij) hi0 hj0 hp

namespace Affine

namespace Simplex

lemma dist_lt_of_mem_closedInterior_of_strictConvexSpace {n : ℕ} (s : Simplex ℝ P n) {r : ℝ}
    {p₀ p : P} (hp : p ∈ s.closedInterior) (hp' : ∀ i, p ≠ s.points i)
    (hr : ∀ i, dist (s.points i) p₀ ≤ r) : dist p p₀ < r := by
  rcases hp with ⟨w, hw, hw01, rfl⟩
  obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
    by_contra! hij
    simp_all
  obtain ⟨j, hij, hj⟩ : ∃ j, i ≠ j ∧ w j ≠ 0 := by
    by_contra! hij
    apply hp' i
    rw [← Finset.univ.affineCombination_affineCombinationSingleWeights ℝ s.points
      (Finset.mem_univ i)]
    congr 1
    ext j
    by_cases hj : j = i
    · simp only [hj, affineCombinationSingleWeights_apply_self]
      rw [← hw, eq_comm]
      exact sum_eq_single i (fun k _ hk ↦ hij k hk.symm) (by simp)
    · rw [affineCombinationSingleWeights_apply_of_ne _ hj]
      exact hij j (Ne.symm hj)
  exact dist_affineCombination_lt_of_strictConvexSpace (fun k _ ↦ (hw01 k).1) hw
    (Finset.mem_univ i) (Finset.mem_univ j) (s.independent.injective.ne hij) hi hj (fun k _ ↦ hr k)

lemma dist_lt_of_mem_interior_of_strictConvexSpace {n : ℕ} (s : Simplex ℝ P n) {r : ℝ}
    {p₀ p : P} (hp : p ∈ s.interior) (hr : ∀ i, dist (s.points i) p₀ ≤ r) : dist p p₀ < r :=
  s.dist_lt_of_mem_closedInterior_of_strictConvexSpace
    (Set.mem_of_mem_of_subset hp s.interior_subset_closedInterior)
    (fun i h ↦ s.point_notMem_interior i (h ▸ hp)) hr

end Simplex

end Affine

end Space
