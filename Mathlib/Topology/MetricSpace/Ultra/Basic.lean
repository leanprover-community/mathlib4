/-
Copyright (c) 2024 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

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
For example, one could say `[Norm K] [Fact (IsNonarchimedean (norm : K → ℝ))]`,

The file imports a later file in the hierarchy of pseudometric spaces, since
`Metric.isClosed_closedBall` and `Metric.isClosed_sphere` is proven in a later file
using more conceptual results.

TODO: Generalize to ultrametric uniformities

## Tags

ultrametric, nonarchimedean
-/

variable {X : Type*}

/-- The `dist : X → X → ℝ` respects the ultrametric inequality
of `dist(x, z) ≤ max (dist(x,y)) (dist(y,z))`. -/
class IsUltrametricDist (X : Type*) [Dist X] : Prop where
  dist_triangle_max : ∀ x y z : X, dist x z ≤ max (dist x y) (dist y z)

open Metric

variable [PseudoMetricSpace X] [IsUltrametricDist X] (x y z : X) (r s : ℝ)

lemma dist_triangle_max : dist x z ≤ max (dist x y) (dist y z) :=
  IsUltrametricDist.dist_triangle_max x y z

namespace IsUltrametricDist

/-- All triangles are isosceles in an ultrametric space. -/
lemma dist_eq_max_of_dist_ne_dist (h : dist x y ≠ dist y z) :
    dist x z = max (dist x y) (dist y z) := by
  apply le_antisymm (dist_triangle_max x y z)
  rcases h.lt_or_gt with h | h
  · rw [max_eq_right h.le]
    apply (le_max_iff.mp <| dist_triangle_max y x z).resolve_left
    simpa only [not_le, dist_comm x y] using h
  · rw [max_eq_left h.le, dist_comm x y, dist_comm x z]
    apply (le_max_iff.mp <| dist_triangle_max y z x).resolve_left
    simpa only [not_le, dist_comm x y] using h

instance subtype (p : X → Prop) : IsUltrametricDist (Subtype p) :=
  ⟨fun _ _ _ ↦ by simpa [Subtype.dist_eq] using dist_triangle_max _ _ _⟩

lemma ball_eq_of_mem {x y : X} {r : ℝ} (h : y ∈ ball x r) : ball x r = ball y r := by
  ext a
  simp_rw [mem_ball] at h ⊢
  constructor <;> intro h' <;>
  exact (dist_triangle_max _ _ _).trans_lt (max_lt h' (dist_comm x _ ▸ h))

lemma mem_ball_iff {x y : X} {r : ℝ} : y ∈ ball x r ↔ x ∈ ball y r := by
  cases lt_or_ge 0 r with
  | inl hr =>
    constructor <;> intro h <;>
    rw [← ball_eq_of_mem h] <;>
    simp [hr]
  | inr hr => simp [ball_eq_empty.mpr hr]

lemma ball_subset_trichotomy :
    ball x r ⊆ ball y s ∨ ball y s ⊆ ball x r ∨ Disjoint (ball x r) (ball y s) := by
  wlog hrs : r ≤ s generalizing x y r s
  · rw [disjoint_comm, ← or_assoc, or_comm (b := _ ⊆ _), or_assoc]
    exact this y x s r (lt_of_not_ge hrs).le
  · refine Set.disjoint_or_nonempty_inter (ball x r) (ball y s) |>.symm.imp (fun h ↦ ?_) (Or.inr ·)
    obtain ⟨hxz, hyz⟩ := (Set.mem_inter_iff _ _ _).mp h.some_mem
    have hx := ball_subset_ball hrs (x := x)
    rwa [ball_eq_of_mem hyz |>.trans (ball_eq_of_mem <| hx hxz).symm]

lemma ball_eq_or_disjoint :
    ball x r = ball y r ∨ Disjoint (ball x r) (ball y r) := by
  refine Set.disjoint_or_nonempty_inter (ball x r) (ball y r) |>.symm.imp (fun h ↦ ?_) id
  have h₁ := ball_eq_of_mem <| Set.inter_subset_left h.some_mem
  have h₂ := ball_eq_of_mem <| Set.inter_subset_right h.some_mem
  exact h₁.trans h₂.symm

lemma closedBall_eq_of_mem {x y: X} {r : ℝ} (h : y ∈ closedBall x r) :
    closedBall x r = closedBall y r := by
  ext
  simp_rw [mem_closedBall] at h ⊢
  constructor <;> intro h' <;>
  exact (dist_triangle_max _ _ _).trans (max_le h' (dist_comm x _ ▸ h))

lemma mem_closedBall_iff {x y: X} {r : ℝ} :
    y ∈ closedBall x r ↔ x ∈ closedBall y r := by
  cases le_or_gt 0 r with
  | inl hr =>
    constructor <;> intro h <;>
    rw [← closedBall_eq_of_mem h] <;>
    simp [hr]
  | inr hr => simp [closedBall_eq_empty.mpr hr]

lemma closedBall_subset_trichotomy :
    closedBall x r ⊆ closedBall y s ∨ closedBall y s ⊆ closedBall x r ∨
    Disjoint (closedBall x r) (closedBall y s) := by
  wlog hrs : r ≤ s generalizing x y r s
  · rw [disjoint_comm, ← or_assoc, or_comm (b := _ ⊆ _), or_assoc]
    exact this y x s r (lt_of_not_ge hrs).le
  · refine Set.disjoint_or_nonempty_inter (closedBall x r) (closedBall y s) |>.symm.imp
      (fun h ↦ ?_) (Or.inr ·)
    obtain ⟨hxz, hyz⟩ := (Set.mem_inter_iff _ _ _).mp h.some_mem
    have hx := closedBall_subset_closedBall hrs (x := x)
    rwa [closedBall_eq_of_mem hyz |>.trans (closedBall_eq_of_mem <| hx hxz).symm]

lemma isClosed_ball (x : X) (r : ℝ) : IsClosed (ball x r) := by
  cases le_or_gt r 0 with
  | inl hr =>
    simp [ball_eq_empty.mpr hr]
  | inr h =>
    rw [← isOpen_compl_iff, isOpen_iff]
    simp only [Set.mem_compl_iff, not_lt, gt_iff_lt]
    intro y hy
    cases ball_eq_or_disjoint x y r with
    | inl hd =>
      rw [hd] at hy
      simp [h.not_ge] at hy
    | inr hd =>
      use r
      simp [h, hy, ← Set.le_iff_subset, le_compl_iff_disjoint_left, hd]

lemma isClopen_ball : IsClopen (ball x r) := ⟨isClosed_ball x r, isOpen_ball⟩

lemma frontier_ball_eq_empty : frontier (ball x r) = ∅ :=
  isClopen_iff_frontier_eq_empty.mp (isClopen_ball x r)

lemma closedBall_eq_or_disjoint :
    closedBall x r = closedBall y r ∨ Disjoint (closedBall x r) (closedBall y r) := by
  refine Set.disjoint_or_nonempty_inter (closedBall x r) (closedBall y r) |>.symm.imp
    (fun h ↦ ?_) id
  have h₁ := closedBall_eq_of_mem <| Set.inter_subset_left h.some_mem
  have h₂ := closedBall_eq_of_mem <| Set.inter_subset_right h.some_mem
  exact h₁.trans h₂.symm

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
      simp [closedBall_eq_of_mem hy, h.not_gt] at hd

lemma isClopen_closedBall {r : ℝ} (hr : r ≠ 0) : IsClopen (closedBall x r) :=
  ⟨Metric.isClosed_closedBall, isOpen_closedBall x hr⟩

lemma frontier_closedBall_eq_empty {r : ℝ} (hr : r ≠ 0) : frontier (closedBall x r) = ∅ :=
  isClopen_iff_frontier_eq_empty.mp (isClopen_closedBall x hr)

lemma isOpen_sphere {r : ℝ} (hr : r ≠ 0) : IsOpen (sphere x r) := by
  rw [← closedBall_diff_ball, sdiff_eq]
  exact (isOpen_closedBall x hr).inter (isClosed_ball x r).isOpen_compl

lemma isClopen_sphere {r : ℝ} (hr : r ≠ 0) : IsClopen (sphere x r) :=
  ⟨Metric.isClosed_sphere, isOpen_sphere x hr⟩

end IsUltrametricDist
