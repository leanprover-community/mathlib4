/-
Copyright (c) 2024 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
module

public import Mathlib.Topology.UniformSpace.Cauchy
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Topology.Algebra.IsUniformGroup.Basic
public import Mathlib.Topology.Algebra.Module.LocallyConvex

/-!
# Totally Bounded sets and Convex Hulls

## Main statements

- `totallyBounded_convexHull`: The convex hull of a totally bounded set is totally bounded.

## References

* [Bourbaki, *Topological Vector Spaces*][bourbaki1987]

## Tags

convex, totally bounded
-/

public section

open Set Pointwise

variable {E : Type*} {s : Set E}
variable [AddCommGroup E] [Module ℝ E]
variable [UniformSpace E] [IsUniformAddGroup E] [LocallyConvexSpace ℝ E] [ContinuousSMul ℝ E]

protected lemma TotallyBounded.convexHull (hs : TotallyBounded s) :
    TotallyBounded (convexHull ℝ s) := by
  rw [totallyBounded_iff_subset_finite_iUnion_nhds_zero] at ⊢ hs
  intro U hU
  obtain ⟨W, hW₁, hW₂⟩ := exists_nhds_zero_half hU
  obtain ⟨V, hV₁,hV₂, hV₃⟩ := (locallyConvexSpace_iff_exists_convex_subset_zero ℝ E).mp ‹_› W hW₁
  obtain ⟨t, htf, hts⟩ := hs _ hV₁
  obtain ⟨t', htf', hts'⟩ := totallyBounded_iff_subset_finite_iUnion_nhds_zero.mp
    (htf.isCompact_convexHull ℝ).totallyBounded _ hV₁
  use t', htf'
  simp only [iUnion_vadd_set, vadd_eq_add] at hts hts' ⊢
  grw [hts, convexHull_add_subset, hV₂.convexHull_eq, hts', add_assoc, hV₃, add_subset_iff.mpr hW₂]

@[simp] lemma totallyBounded_convexHull : TotallyBounded (convexHull ℝ s) ↔ TotallyBounded s where
  mp := .subset <| subset_convexHull ..
  mpr := .convexHull
