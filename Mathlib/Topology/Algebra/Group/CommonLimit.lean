/-
Copyright (c) 2026 Fernando M. Reich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando M. Reich
-/
module

public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Common limits of an indexed family of functions along a filter

Given a family of functions `u : ι → α → E`, a set of indices `s`, and a filter
`F` on the domain `α`, a point `L : E` is a *common limit* of the family along
`F` if every selected function `u i` (for `i ∈ s`) tends to `L` along `F`.

This file records an elementary principle. When `E` is a Hausdorff topological
additive group and `F` is nontrivial, individual convergence of the members
together with vanishing of all pairwise differences forces the members to share
a single limit, and that common limit is unique.

## Main definitions

* `Filter.IsCommonLimit u s F L`: every `u i` with `i ∈ s` tends to `L` along `F`.

## Main results

* `Filter.IsCommonLimit.unique`: over a nonempty index set, along a nontrivial
  filter, into a Hausdorff space, a common limit is unique. This uses no
  algebraic structure on `E`.
* `Filter.tendsto_eq_of_tendsto_sub_nhds_zero`: if `f → a`, `g → b`, and
  `f - g → 0` along a nontrivial filter into a Hausdorff topological additive
  group, then `a = b`.
* `Filter.exists_isCommonLimit_of_pairwise_tendsto_sub_nhds_zero`: individual
  convergence together with vanishing pairwise differences yields a common
  limit. Individual convergence is a hypothesis: vanishing differences alone do
  not force convergence.
* `Filter.existsUnique_isCommonLimit_of_pairwise_tendsto_sub_nhds_zero`: the same
  hypotheses yield a unique common limit.
-/

public section

open scoped Topology

namespace Filter

variable {ι : Type*} {α : Type*} {E : Type*}

/-- `L` is a common limit of the family `u` over the index set `s` along the
filter `F`: every selected function `u i` (with `i ∈ s`) tends to `L`. -/
def IsCommonLimit [TopologicalSpace E]
    (u : ι → α → E) (s : Set ι) (F : Filter α) (L : E) : Prop :=
  ∀ i ∈ s, Tendsto (u i) F (𝓝 L)

/-- A common limit is unique: over a nonempty index set, along a nontrivial
filter, into a Hausdorff space, two common limits coincide. -/
theorem IsCommonLimit.unique [TopologicalSpace E] [T2Space E]
    {u : ι → α → E} {s : Set ι} {F : Filter α} [F.NeBot] {L₁ L₂ : E}
    (hs : s.Nonempty)
    (h₁ : IsCommonLimit u s F L₁) (h₂ : IsCommonLimit u s F L₂) :
    L₁ = L₂ := by
  obtain ⟨i, hi⟩ := hs
  exact tendsto_nhds_unique (h₁ i hi) (h₂ i hi)

/-- If `f → a`, `g → b`, and `f - g → 0` along a nontrivial filter into a
Hausdorff topological additive group, then `a = b`. This is the elementary
"subtract the limits, use uniqueness of limits" argument, packaged once. -/
theorem tendsto_eq_of_tendsto_sub_nhds_zero [TopologicalSpace E] [AddCommGroup E]
    [IsTopologicalAddGroup E] [T2Space E]
    {F : Filter α} [F.NeBot] {f g : α → E} {a b : E}
    (hf : Tendsto f F (𝓝 a))
    (hg : Tendsto g F (𝓝 b))
    (hsub : Tendsto (fun x => f x - g x) F (𝓝 0)) :
    a = b := by
  have hsub' : Tendsto (fun x => f x - g x) F (𝓝 (a - b)) := hf.sub hg
  have hzero : a - b = 0 := tendsto_nhds_unique hsub' hsub
  exact sub_eq_zero.mp hzero

/-- Existence of a common limit from individual convergence and vanishing
pairwise differences. Fix any index `i₀ ∈ s` with limit `L₀`; for every other
index the pairwise hypothesis forces its limit to equal `L₀`.

Individual convergence is a genuine hypothesis: vanishing pairwise differences
alone never force convergence. -/
theorem exists_isCommonLimit_of_pairwise_tendsto_sub_nhds_zero
    [TopologicalSpace E] [AddCommGroup E] [IsTopologicalAddGroup E] [T2Space E]
    {u : ι → α → E} {s : Set ι} {F : Filter α} [F.NeBot]
    (hs : s.Nonempty)
    (hindividual : ∀ i ∈ s, ∃ L, Tendsto (u i) F (𝓝 L))
    (hpairwise : ∀ i ∈ s, ∀ j ∈ s, Tendsto (fun x => u i x - u j x) F (𝓝 0)) :
    ∃ L, IsCommonLimit u s F L := by
  obtain ⟨i₀, hi₀⟩ := hs
  obtain ⟨L₀, hL₀⟩ := hindividual i₀ hi₀
  refine ⟨L₀, ?_⟩
  intro j hj
  obtain ⟨Lj, hLj⟩ := hindividual j hj
  have hpw := hpairwise i₀ hi₀ j hj
  have heq : L₀ = Lj := tendsto_eq_of_tendsto_sub_nhds_zero hL₀ hLj hpw
  rw [heq]
  exact hLj

/-- Existence and uniqueness of a common limit from individual convergence and
vanishing pairwise differences. -/
theorem existsUnique_isCommonLimit_of_pairwise_tendsto_sub_nhds_zero
    [TopologicalSpace E] [AddCommGroup E] [IsTopologicalAddGroup E] [T2Space E]
    {u : ι → α → E} {s : Set ι} {F : Filter α} [F.NeBot]
    (hs : s.Nonempty)
    (hindividual : ∀ i ∈ s, ∃ L, Tendsto (u i) F (𝓝 L))
    (hpairwise : ∀ i ∈ s, ∀ j ∈ s, Tendsto (fun x => u i x - u j x) F (𝓝 0)) :
    ∃! L, IsCommonLimit u s F L := by
  obtain ⟨L, hL⟩ :=
    exists_isCommonLimit_of_pairwise_tendsto_sub_nhds_zero hs hindividual hpairwise
  exact ⟨L, hL, fun L' hL' => IsCommonLimit.unique hs hL' hL⟩

end Filter
