/-
Copyright (c) 2024 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/

import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Analysis.Convex.Hull
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.Algebra.Module.LocallyConvex

/-!
# Totally Bounded sets and Convex Hulls

## Main statements

- `totallyBounded_convexHull` The convex hull of a totally bounded set is totally bounded.

## References

* [Bourbaki, *Topological Vector Spaces*][bourbaki1987]

## Tags

convex, totally bounded
-/

open Set Pointwise

variable (E : Type*) {s : Set E}
variable [AddCommGroup E] [Module ℝ E]
variable [UniformSpace E] [IsUniformAddGroup E] [lcs : LocallyConvexSpace ℝ E] [ContinuousSMul ℝ E]

theorem totallyBounded_convexHull (hs : TotallyBounded s) :
    TotallyBounded (convexHull ℝ s) := by
  rw [totallyBounded_iff_subset_finite_iUnion_nhds_zero]
  intro U hU
  obtain ⟨W, hW₁, hW₂⟩ := exists_nhds_zero_half hU
  obtain ⟨V, ⟨hV₁, hV₂, hV₃⟩⟩ := (locallyConvexSpace_iff_exists_convex_subset_zero ℝ E).mp lcs W hW₁
  obtain ⟨t, ⟨htf, hts⟩⟩ := (totallyBounded_iff_subset_finite_iUnion_nhds_zero.mp hs) _ hV₁
  obtain ⟨t', ⟨htf', hts'⟩⟩ := (totallyBounded_iff_subset_finite_iUnion_nhds_zero.mp
    (IsCompact.totallyBounded (Finite.isCompact_convexHull htf)) _ hV₁)
  use t', htf'
  simp only [iUnion_vadd_set, vadd_eq_add] at hts hts' ⊢
  calc convexHull ℝ s
    _ ⊆ convexHull ℝ (t + V) := convexHull_mono hts
    _ ⊆ convexHull ℝ t + convexHull ℝ V := convexHull_add_subset
    _ = convexHull ℝ t + V := by rw [hV₂.convexHull_eq]
    _ ⊆ t' + V + V := add_subset_add_right hts'
    _ = t' + (V + V) := by rw [add_assoc]
    _ ⊆ t' + (W + W) := add_subset_add_left (add_subset_add hV₃ hV₃)
    _ ⊆ t' + U := add_subset_add_left (add_subset_iff.mpr hW₂)
