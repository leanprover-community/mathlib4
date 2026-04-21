/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.TangentCone.Defs
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.Topology.Algebra.Monoid
import Mathlib.Analysis.Calculus.TangentCone.Basic

/-!
# Product of sets with unique differentiability property

In this file we prove that the product of two sets with unique differentiability property
has the same property, see `UniqueDiffOn.prod`.
-/
set_option backward.defeqAttrib.useBackward true

public section

open Filter Set
open scoped Topology

variable {𝕜 E F : Type*} [Semiring 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [ContinuousAdd E] [ContinuousConstSMul 𝕜 E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [ContinuousAdd F] [ContinuousConstSMul 𝕜 F]
  {x : E} {s : Set E} {y : F} {t : Set F}

/-- The tangent cone of a product contains the tangent cone of its left factor. -/
theorem subset_tangentConeAt_prod_left (ht : y ∈ closure t) :
    LinearMap.inl 𝕜 E F '' tangentConeAt 𝕜 s x ⊆ tangentConeAt 𝕜 (s ×ˢ t) (x, y) := by
  rw [← tangentConeAt_closure (s := s ×ˢ t), closure_prod_eq]
  rintro _ ⟨z, hz, rfl⟩
  rcases exists_fun_of_mem_tangentConeAt hz with ⟨ι, l, hl, c, d, hd₀, hds, hcd⟩
  refine mem_tangentConeAt_of_seq l c (fun n ↦ (d n, 0)) (hd₀.prodMk_nhds tendsto_const_nhds)
    (hds.mono fun n hn ↦ by simp [ht, subset_closure hn]) ?_
  simpa using hcd.prodMk_nhds tendsto_const_nhds

/-- The tangent cone of a product contains the tangent cone of its right factor. -/
theorem subset_tangentConeAt_prod_right (hs : x ∈ closure s) :
    LinearMap.inr 𝕜 E F '' tangentConeAt 𝕜 t y ⊆ tangentConeAt 𝕜 (s ×ˢ t) (x, y) := by
  rw [← tangentConeAt_closure (s := s ×ˢ t), closure_prod_eq]
  rintro _ ⟨z, hz, rfl⟩
  rcases exists_fun_of_mem_tangentConeAt hz with ⟨ι, l, hl, c, d, hd₀, hds, hcd⟩
  refine mem_tangentConeAt_of_seq l c (fun n ↦ (0, d n)) (tendsto_const_nhds.prodMk_nhds hd₀)
    (hds.mono fun n hn ↦ by simp [hs, subset_closure hn]) ?_
  simpa using tendsto_const_nhds.prodMk_nhds hcd

/-- The product of two sets of unique differentiability at points `x` and `y` has unique
differentiability at `(x, y)`. -/
theorem UniqueDiffWithinAt.prod (hs : UniqueDiffWithinAt 𝕜 s x)
    (ht : UniqueDiffWithinAt 𝕜 t y) : UniqueDiffWithinAt 𝕜 (s ×ˢ t) (x, y) := by
  rw [uniqueDiffWithinAt_iff] at hs ht ⊢
  rw [closure_prod_eq]
  refine ⟨?_, hs.2, ht.2⟩
  have : _ ≤ Submodule.span 𝕜 (tangentConeAt 𝕜 (s ×ˢ t) (x, y)) := Submodule.span_mono
    (union_subset (subset_tangentConeAt_prod_left ht.2) (subset_tangentConeAt_prod_right hs.2))
  rw [LinearMap.span_inl_union_inr, SetLike.le_def] at this
  exact (hs.1.prod ht.1).mono this

/-- The product of two sets of unique differentiability is a set of unique differentiability. -/
theorem UniqueDiffOn.prod (hs : UniqueDiffOn 𝕜 s) (ht : UniqueDiffOn 𝕜 t) :
    UniqueDiffOn 𝕜 (s ×ˢ t) :=
  fun ⟨x, y⟩ h => UniqueDiffWithinAt.prod (hs x h.1) (ht y h.2)
