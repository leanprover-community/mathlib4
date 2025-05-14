/-
Copyright (c) 2025 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Analysis.Calculus.TangentCone

/-!
# Unique differentiability near a point

In this file we define a predicate `UniqueDiffNear 𝕜 s x`
saying that differential within `s` at all points `y ∈ s` near `x` is unique.
This assumption implies uniqueness of higher order derivatives within `s` at `x`.
-/

open Filter Function Set
open scoped Topology

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] {s t : Set E} {x y : E}

variable (𝕜) in
/-- This predicate says that differential within `s` at all points `y ∈ s` near `x` is unique.

This assumption implies uniqueness of higher order derivatives within `s` at `x`. -/
@[mk_iff uniqueDiffNear_iff_eventually_insert]
structure UniqueDiffNear (s : Set E) (x : E) : Prop where of_eventually_insert ::
  eventually_insert : ∀ᶠ y in 𝓝[insert x s] x, UniqueDiffWithinAt 𝕜 s y

theorem UniqueDiffNear.iff_uniqueDiffWithinAt_and_eventually :
    UniqueDiffNear 𝕜 s x ↔
      UniqueDiffWithinAt 𝕜 s x ∧ ∀ᶠ y in 𝓝[s] x, UniqueDiffWithinAt 𝕜 s y := by
  simp [uniqueDiffNear_iff_eventually_insert]

theorem UniqueDiffNear.uniqueDiffWithinAt (h : UniqueDiffNear 𝕜 s x) :
    UniqueDiffWithinAt 𝕜 s x :=
  (iff_uniqueDiffWithinAt_and_eventually.mp h).1

theorem UniqueDiffNear.eventually (h : UniqueDiffNear 𝕜 s x) :
    ∀ᶠ y in 𝓝[s] x, UniqueDiffWithinAt 𝕜 s y :=
  (iff_uniqueDiffWithinAt_and_eventually.mp h).2

theorem UniqueDiffNear.of_uniqueDiffWithinAt_of_eventually (h₁ : UniqueDiffWithinAt 𝕜 s x)
    (h₂ : ∀ᶠ y in 𝓝[s] x, UniqueDiffWithinAt 𝕜 s y) : UniqueDiffNear 𝕜 s x :=
    iff_uniqueDiffWithinAt_and_eventually.mpr ⟨h₁, h₂⟩

theorem UniqueDiffOn.uniqueDiffNear (h : UniqueDiffOn 𝕜 s) (hx : x ∈ s) :
    UniqueDiffNear 𝕜 s x :=
  .of_uniqueDiffWithinAt_of_eventually (h _ hx) <| eventually_mem_nhdsWithin.mono h

theorem eventually_insert_uniqueDiffNear :
    (∀ᶠ y in 𝓝[insert x s] x, UniqueDiffNear 𝕜 s y) ↔ UniqueDiffNear 𝕜 s x := by
  simp [uniqueDiffNear_iff_eventually_insert]

alias ⟨_, UniqueDiffNear.eventually_insert'⟩ := eventually_insert_uniqueDiffNear

theorem UniqueDiffNear.eventually' (h : UniqueDiffNear 𝕜 s x) :
    ∀ᶠ y in 𝓝[s] x, UniqueDiffNear 𝕜 s y :=
  h.eventually_insert'.filter_mono <| by gcongr; apply subset_insert

theorem UniqueDiffNear.exists_uniqueDiffOn_subset (h : UniqueDiffNear 𝕜 s x) (ht : t ∈ 𝓝[s] x) :
    ∃ u ∈ 𝓝[s] x, UniqueDiffOn 𝕜 (insert x u) ∧ u ⊆ t := by
  rcases mem_nhdsWithin.mp (inter_mem h.eventually ht) with ⟨U, hUo, hxU, hU⟩
  rw [subset_inter_iff] at hU
  refine ⟨U ∩ s, mem_nhdsWithin.mpr ⟨U, hUo, hxU, Subset.rfl⟩, ?_, hU.2⟩
  rintro y (rfl | hy)
  · have := h.uniqueDiffWithinAt.inter (hUo.mem_nhds hxU)
