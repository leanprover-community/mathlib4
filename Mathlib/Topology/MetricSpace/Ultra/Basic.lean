/-
Copyright (c) 2024 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
## Ultrametric spaces

This file defines ultrametric spaces, implemented as a mixin on the `Dist`,
so that it can apply on pseudometric spaces as well.

## Main definitions

* `IsUltrametricDist X`: Annotates `dist : X → X → ℝ` as respecting the ultrametric inequality
  of `dist(x, z) ≤ max {dist(x,y), dist(y,z)}`

## Implementation details

The mixin could have been defined as a hypothesis to be carried around, instead of relying on
typeclass synthesis. However, since we declare a (pseudo)metric space on a type using
typeclass arguments, one can declare the ultrametricity at the same time.

TODO: Generalize to ultrametric uniformities

## Tags

ultrametric, nonarchimedean
-/

variable {X : Type*}

/-- The `dist : X → X → ℝ` respects the ultrametric inequality
of `dist(x, z) ≤ max (dist(x,y)) (dist(y,z))`. -/
class IsUltrametricDist (X : Type*) [Dist X] : Prop where
  dist_triangle_max : ∀ x y z : X, dist x z ≤ max (dist x y) (dist y z)

section TODO

lemma Metric.isClosed_closedBall [PseudoMetricSpace X] (x : X) (r : ℝ) :
    IsClosed (closedBall x r) := by
  rw [← isOpen_compl_iff, isOpen_iff]
  simp only [Set.mem_compl_iff, mem_closedBall, not_le]
  intro y hy
  use (dist y x - r) / 2
  simp only [gt_iff_lt, sub_pos, hy, div_pos_iff_of_pos_left, Nat.ofNat_pos, true_and]
  intro z
  simp only [mem_ball, Set.mem_compl_iff, mem_closedBall]
  intro hz H
  rw [lt_div_iff zero_lt_two, mul_two, lt_sub_iff_add_lt] at hz
  have := dist_triangle y z x
  refine lt_irrefl (dist y x) (hz.trans_le' (this.trans ?_))
  rw [dist_comm, add_assoc, add_le_add_iff_left]
  refine H.trans ?_
  simp [dist_nonneg]

end TODO

open Metric

variable [PseudoMetricSpace X] [IsUltrametricDist X] (x y z : X) (r s : ℝ)

lemma dist_triangle_max : dist x z ≤ max (dist x y) (dist y z) :=
  IsUltrametricDist.dist_triangle_max x y z

namespace IsUltrametricDist

lemma ball_eq_of_mem {x y : X} {r : ℝ} (h : y ∈ ball x r) : ball x r = ball y r := by
  ext a
  simp_rw [mem_ball] at h ⊢
  constructor <;> intro h' <;>
  exact (dist_triangle_max _ _ _).trans_lt (max_lt h' (dist_comm x _ ▸ h))

lemma mem_ball_iff_mem_ball {x y: X} {r : ℝ} : y ∈ ball x r ↔ x ∈ ball y r := by
  cases lt_or_le 0 r with
  | inl hr =>
    constructor <;> intro h <;>
    rw [← ball_eq_of_mem h] <;>
    simp [hr]
  | inr hr => simp [ball_eq_empty.mpr hr]

lemma closedBall_eq_of_mem {x y: X} {r : ℝ} (h : y ∈ closedBall x r) :
    closedBall x r = closedBall y r := by
  ext
  simp_rw [mem_closedBall] at h ⊢
  constructor <;> intro h' <;>
  exact (dist_triangle_max _ _ _).trans (max_le h' (dist_comm x _ ▸ h))

lemma mem_closedBall_iff_mem_closedBall {x y: X} {r : ℝ} :
    y ∈ closedBall x r ↔ x ∈ closedBall y r := by
  cases le_or_lt 0 r with
  | inl hr =>
    constructor <;> intro h <;>
    rw [← closedBall_eq_of_mem h] <;>
    simp [hr]
  | inr hr => simp [closedBall_eq_empty.mpr hr]

lemma ball_subset_trichotomy :
    ball x r ⊆ ball y s ∨ ball y s ⊆ ball x r ∨ Disjoint (ball x r) (ball y s) := by
  cases le_or_lt r s with
  | inl h =>
    cases le_or_lt s (dist x y) with
    | inl h' =>
      refine Or.inr (Or.inr ?_)
      intro S hsx hsy z hz
      suffices y ∈ ball x s by
        refine h'.not_lt ?_
        simpa [dist_comm] using this
      have hx : x ∈ ball z s := by
        rw [mem_ball_iff_mem_ball]
        exact ball_subset_ball h (hsx hz)
      rw [← ball_eq_of_mem hx, mem_ball_iff_mem_ball]
      exact hsy hz
    | inr h' =>
      refine Or.inl ?_
      rw [ball_eq_of_mem (mem_ball.mpr h')]
      exact ball_subset_ball h
  | inr h =>
    cases le_or_lt r (dist x y) with
    | inl h' =>
      refine Or.inr (Or.inr ?_)
      intro S hsx hsy z hz
      suffices y ∈ ball x r by
        refine h'.not_lt ?_
        simpa [dist_comm] using this
      have hx : x ∈ ball z r := by
        rw [mem_ball_iff_mem_ball]
        exact hsx hz
      rw [← ball_eq_of_mem hx, mem_ball_iff_mem_ball]
      exact ball_subset_ball h.le (hsy hz)
    | inr h' =>
      refine Or.inr (Or.inl ?_)
      rw [← ball_eq_of_mem (mem_ball.mpr h')]
      exact ball_subset_ball h.le

lemma ball_eq_or_disjoint :
    ball x r = ball y r ∨ Disjoint (ball x r) (ball y r) := by
  cases le_or_lt r 0 with
  | inl hr =>
    simp [ball_eq_empty.mpr hr]
  | inr hr =>
    rcases ball_subset_trichotomy x y r r with h|h|h
    · refine Or.inl ?_
      rw [ball_eq_of_mem (h (mem_ball_self hr))]
    · refine Or.inl ?_
      rw [ball_eq_of_mem (h (mem_ball_self hr))]
    · exact Or.inr h

lemma isClosed_ball (x : X) (r : ℝ) : IsClosed (ball x r) := by
  cases le_or_lt r 0 with
  | inl hr =>
    simp [ball_eq_empty.mpr hr]
  | inr h =>
    rw [← isOpen_compl_iff, isOpen_iff]
    simp only [Set.mem_compl_iff, not_lt, gt_iff_lt]
    intro y hy
    cases ball_eq_or_disjoint x y r with
    | inl hd =>
      rw [hd] at hy
      simp [h.not_le] at hy
    | inr hd =>
      use r
      simp [h, hy, ← Set.le_iff_subset, le_compl_iff_disjoint_left, hd]

lemma isClopen_ball : IsClopen (ball x r) := ⟨isClosed_ball x r, isOpen_ball⟩

lemma frontier_ball_eq_empty : frontier (ball x r) = ∅ :=
  isClopen_iff_frontier_eq_empty.mp (isClopen_ball x r)

lemma closedBall_subset_trichotomy :
    closedBall x r ⊆ closedBall y s ∨ closedBall y s ⊆ closedBall x r ∨
    Disjoint (closedBall x r) (closedBall y s) := by
  cases le_or_lt r s with
  | inl h =>
    cases lt_or_le s (dist x y) with
    | inl h' =>
      refine Or.inr (Or.inr ?_)
      intro S hsx hsy z hz
      suffices y ∈ closedBall x s by
        refine h'.not_le ?_
        simpa [dist_comm] using this
      have hx : x ∈ closedBall z s := by
        rw [mem_closedBall_iff_mem_closedBall]
        exact closedBall_subset_closedBall h (hsx hz)
      rw [← closedBall_eq_of_mem hx, mem_closedBall_iff_mem_closedBall]
      exact hsy hz
    | inr h' =>
      refine Or.inl ?_
      rw [closedBall_eq_of_mem (mem_closedBall.mpr h')]
      exact closedBall_subset_closedBall h
  | inr h =>
    cases lt_or_le r (dist x y) with
    | inl h' =>
      refine Or.inr (Or.inr ?_)
      intro S hsx hsy z hz
      suffices y ∈ closedBall x r by
        refine h'.not_le ?_
        simpa [dist_comm] using this
      have hx : x ∈ closedBall z r := by
        rw [mem_closedBall_iff_mem_closedBall]
        exact hsx hz
      rw [← closedBall_eq_of_mem hx, mem_closedBall_iff_mem_closedBall]
      exact closedBall_subset_closedBall h.le (hsy hz)
    | inr h' =>
      refine Or.inr (Or.inl ?_)
      rw [← closedBall_eq_of_mem (mem_closedBall.mpr h')]
      exact closedBall_subset_closedBall h.le

lemma closedBall_eq_or_disjoint :
    closedBall x r = closedBall y r ∨ Disjoint (closedBall x r) (closedBall y r) := by
  cases lt_or_le r 0 with
  | inl hr =>
    simp [closedBall_eq_empty.mpr hr]
  | inr hr =>
    rcases closedBall_subset_trichotomy x y r r with h|h|h
    · refine Or.inl ?_
      rw [closedBall_eq_of_mem (h (mem_closedBall_self hr))]
    · refine Or.inl ?_
      rw [closedBall_eq_of_mem (h (mem_closedBall_self hr))]
    · exact Or.inr h

lemma isOpen_closedBall {r : ℝ} (hr : r ≠ 0) : IsOpen (closedBall x r) := by
  cases lt_or_gt_of_ne hr with
  | inl h =>
    simp [closedBall_eq_empty.mpr h]
  | inr h =>
    rw [isOpen_iff]
    simp only [Set.mem_compl_iff, not_lt, gt_iff_lt]
    intro y hy
    cases closedBall_eq_or_disjoint x y r with
    | inl hd =>
      use r
      simp [h, hd, ball_subset_closedBall]
    | inr hd =>
      simp [closedBall_eq_of_mem hy, h.not_lt] at hd

lemma isClopen_closedBall {r : ℝ} (hr : r ≠ 0) : IsClopen (closedBall x r) :=
  ⟨isClosed_closedBall x r, isOpen_closedBall x hr⟩

lemma frontier_closedBall_eq_empty {r : ℝ} (hr : r ≠ 0) : frontier (closedBall x r) = ∅ :=
  isClopen_iff_frontier_eq_empty.mp (isClopen_closedBall x hr)

lemma isOpen_sphere {r : ℝ} (hr : r ≠ 0) : IsOpen (sphere x r) := by
  rw [← closedBall_diff_ball, sdiff_eq]
  exact (isOpen_closedBall x hr).inter (isClosed_ball x r).isOpen_compl

lemma isClosed_sphere : IsClosed (sphere x r) := by
  rw [← closedBall_diff_ball, sdiff_eq]
  exact (isClosed_closedBall x r).inter isOpen_ball.isClosed_compl

lemma isClopen_sphere {r : ℝ} (hr : r ≠ 0) : IsClopen (sphere x r) :=
  ⟨isClosed_sphere x r, isOpen_sphere x hr⟩

end IsUltrametricDist
