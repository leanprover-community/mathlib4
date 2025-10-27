/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Order.Filter.Pointwise

/-!
# Tangent cone

In this file, we define two predicates `UniqueDiffWithinAt 𝕜 s x` and `UniqueDiffOn 𝕜 s`
ensuring that, if a function has two derivatives, then they have to coincide. As a direct
definition of this fact (quantifying on all target types and all functions) would depend on
universes, we use a more intrinsic definition: if all the possible tangent directions to the set
`s` at the point `x` span a dense subset of the whole subset, it is easy to check that the
derivative has to be unique.

Therefore, we introduce the set of all tangent directions, named `tangentConeAt`,
and express `UniqueDiffWithinAt` and `UniqueDiffOn` in terms of it.
One should however think of this definition as an implementation detail: the only reason to
introduce the predicates `UniqueDiffWithinAt` and `UniqueDiffOn` is to ensure the uniqueness
of the derivative. This is why their names reflect their uses, and not how they are defined.

## Implementation details

Note that this file is imported by `Mathlib/Analysis/Calculus/FDeriv/Basic.lean`. Hence, derivatives
are not defined yet. The property of uniqueness of the derivative is therefore proved in
`Mathlib/Analysis/Calculus/FDeriv/Basic.lean`, but based on the properties of the tangent cone we
prove here.
-/

open Filter Set Metric
open scoped Topology Pointwise

universe u v
variable (R : Type u) {E : Type v}

section TangentConeAt

variable [AddCommMonoid E] [SMul R E] [TopologicalSpace E] {s : Set E} {x y : E}

/-- The set of all tangent directions to the set `s` at the point `x`. -/
def tangentConeAt (s : Set E) (x : E) : Set E :=
  {y : E | ClusterPt y ((⊤ : Filter R) • 𝓝[(x + ·) ⁻¹' s] 0)}

variable {R}

theorem mem_tangentConeAt_of_seq {α : Type*} {l : Filter α} [l.NeBot] {c : α → R} {d : α → E}
    (hd₀ : Tendsto d l (𝓝 0)) (hds : ∀ᶠ n in l, x + d n ∈ s)
    (hcd : Tendsto (fun n ↦ c n • d n) l (𝓝 y)) : y ∈ tangentConeAt R s x :=
  have : Tendsto (fun n ↦ c n • d n) l ((⊤ : Filter R) • 𝓝[(x + ·) ⁻¹' s] 0) := by
    rw [← map₂_smul, ← map_prod_eq_map₂]
    exact tendsto_map.comp (tendsto_top.prodMk (tendsto_nhdsWithin_iff.mpr ⟨hd₀, hds⟩))
  ClusterPt.mono hcd.mapClusterPt this

theorem exists_fun_of_mem_tangentConeAt (h : y ∈ tangentConeAt R s x) :
    ∃ (α : Type (max u v)) (l : Filter α) (_hl : l.NeBot) (c : α → R) (d : α → E),
      Tendsto d l (𝓝 0) ∧ (∀ᶠ n in l, x + d n ∈ s) ∧ Tendsto (fun n ↦ c n • d n) l (𝓝 y) := by
  rw [tangentConeAt, mem_setOf, ← map₂_smul, ← map_prod_eq_map₂, ClusterPt,
    ← neBot_inf_comap_iff_map'] at h
  refine ⟨R × E, _, h, Prod.fst, Prod.snd, ?_, ?_, ?_⟩
  · refine (tendsto_snd (f := ⊤)).mono_left <| inf_le_right.trans <| ?_
    gcongr
    apply nhdsWithin_le_nhds
  · refine .filter_mono inf_le_right ?_
    rw [top_prod, eventually_comap]
    filter_upwards [eventually_mem_nhdsWithin]
    simp +contextual
  · exact tendsto_comap.mono_left inf_le_left

end TangentConeAt

variable [Semiring R] [AddCommMonoid E] [Module R E] [TopologicalSpace E]

/-- A property ensuring that the tangent cone to `s` at `x` spans a dense subset of the whole space.
The main role of this property is to ensure that the differential within `s` at `x` is unique,
hence this name. The uniqueness it asserts is proved in `UniqueDiffWithinAt.eq` in
`Mathlib/Analysis/Calculus/FDeriv/Basic.lean`.
To avoid pathologies in dimension 0, we also require that `x` belongs to the closure of `s` (which
is automatic when `E` is not `0`-dimensional). -/
@[mk_iff]
structure UniqueDiffWithinAt (s : Set E) (x : E) : Prop where
  dense_tangentConeAt : Dense (Submodule.span R (tangentConeAt R s x) : Set E)
  mem_closure : x ∈ closure s

@[deprecated (since := "2025-04-27")]
alias UniqueDiffWithinAt.dense_tangentCone := UniqueDiffWithinAt.dense_tangentConeAt

/-- A property ensuring that the tangent cone to `s` at any of its points spans a dense subset of
the whole space. The main role of this property is to ensure that the differential along `s` is
unique, hence this name. The uniqueness it asserts is proved in `UniqueDiffOn.eq` in
`Mathlib/Analysis/Calculus/FDeriv/Basic.lean`. -/
def UniqueDiffOn (s : Set E) : Prop :=
  ∀ x ∈ s, UniqueDiffWithinAt R s x
