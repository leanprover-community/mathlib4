/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Order.Filter.Pointwise
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Data.NNReal.Defs
public import Mathlib.Topology.Defs.Filter
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Init
import Mathlib.Order.Filter.Map
import Mathlib.Order.Filter.Prod
import Mathlib.Order.Filter.Tendsto
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Topology.ClusterPt
import Mathlib.Topology.NhdsWithin

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

@[expose] public section

open Filter Set Metric
open scoped Topology Pointwise

universe u v
variable (R : Type u) {E : Type v}

section TangentConeAt

variable [AddCommGroup E] [SMul R E] [TopologicalSpace E] {s : Set E} {x y : E}

/-- The set of all tangent directions to the set `s` at the point `x`.

A point `y` belongs to the tangent cone of `s` at `x` iff
there exist a family of scalars `c n`, a family of vectors `d n`,
and a nontrivial filter in the index type such that

- `d n → 0` along the filter;
- `x + d n ∈ s` eventually along the filter;
- `c n • d n → y` along the filter,

The actual definition is given in terms of cluster points of a filter,
see `mem_tangentConeAt_of_seq` and `exists_fun_of_mem_tangentConeAt`
for the two implications unfolding this definition in more convenient way.

In a space with first countable topology,
one can assume that the index type is `ℕ` and the filter is `atTop`,
but the definition we use is more useful without that assumption.
-/
irreducible_def tangentConeAt (s : Set E) (x : E) : Set E :=
  {y : E | ClusterPt y ((⊤ : Filter R) • 𝓝[(x + ·) ⁻¹' s] 0)}

variable {R}

/-- Let `c n` be a family of scalars, `d n` be a family of vectors, and `l` be a filter such that

- `d n → 0` along `l`;
- `x + d n ∈ s` frequently along `l`;
- `c n • d n → y` along `l`.

Then `y` belongs to the tangent cone of `s` at `x`.
See also

- `mem_tangentConeAt_of_seq` for a version assuming that `x + d n ∈ s` eventually along `l`.
- `exists_fun_of_mem_tangentConeAt` for the other implication.
-/
theorem mem_tangentConeAt_of_frequently {α : Type*} (l : Filter α) (c : α → R) (d : α → E)
    (hd₀ : Tendsto d l (𝓝 0)) (hds : ∃ᶠ n in l, x + d n ∈ s)
    (hcd : Tendsto (fun n ↦ c n • d n) l (𝓝 y)) : y ∈ tangentConeAt R s x := by
  suffices Tendsto (fun n ↦ c n • d n) (l ⊓ 𝓟 {y | x + d y ∈ s}) (⊤ • 𝓝[(x + ·) ⁻¹' s] 0) by
    rw [frequently_iff_neBot] at hds
    rw [tangentConeAt_def]
    exact ClusterPt.mono (hcd.mono_left inf_le_left).mapClusterPt this
  rw [← map₂_smul, ← map_prod_eq_map₂]
  refine tendsto_map.comp (tendsto_top.prodMk (tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩))
  · exact hd₀.mono_left inf_le_left
  · simp [eventually_inf_principal]

/-- A special case of `mem_tangentConeAt_of_frequently`, which avoids `Filter.Frequently`. -/
theorem mem_tangentConeAt_of_seq {α : Type*} (l : Filter α) [l.NeBot] (c : α → R) (d : α → E)
    (hd₀ : Tendsto d l (𝓝 0)) (hds : ∀ᶠ n in l, x + d n ∈ s)
    (hcd : Tendsto (fun n ↦ c n • d n) l (𝓝 y)) : y ∈ tangentConeAt R s x :=
  mem_tangentConeAt_of_frequently l c d hd₀ hds.frequently hcd

/-- If `y` belongs to the tangent cone of `s` at `x`, then there exist

- an index type `α` and a nontrivial filter `l` on `α`;
- a family of scalars `c n`, `n : α`, and a family of vectors `d n`, `n : α` such that
- `d n → 0` along `l`;
- `x + d n ∈ s` eventually along `l`;
- `c n • d n → y` along `l`.

In fact, one can take `α = R × E`, `c = Prod.fst`, and `d = Prod.snd`, but this is not important,
so the lemma statement hides these details.

This lemma provides a convenient way to unfold the definition of `tangentConeAt`. -/
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

/-- "Positive" tangent cone to `s` at `x`. -/
abbrev posTangentConeAt [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] (s : Set E) (x : E) :
    Set E :=
  tangentConeAt NNReal s x

variable [Semiring R] [AddCommGroup E] [Module R E] [TopologicalSpace E]

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

/-- A property ensuring that the tangent cone to `s` at any of its points spans a dense subset of
the whole space. The main role of this property is to ensure that the differential along `s` is
unique, hence this name. The uniqueness it asserts is proved in `UniqueDiffOn.eq` in
`Mathlib/Analysis/Calculus/FDeriv/Basic.lean`. -/
def UniqueDiffOn (s : Set E) : Prop :=
  ∀ x ∈ s, UniqueDiffWithinAt R s x

variable {R} in
theorem UniqueDiffOn.uniqueDiffWithinAt {s : Set E} {x} (hs : UniqueDiffOn R s) (h : x ∈ s) :
    UniqueDiffWithinAt R s x :=
  hs x h
