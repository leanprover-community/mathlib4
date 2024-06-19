/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Topology.PartitionOfUnity
import Mathlib.Analysis.Convex.Combination

#align_import analysis.convex.partition_of_unity from "leanprover-community/mathlib"@"f2ce6086713c78a7f880485f7917ea547a215982"

/-!
# Partition of unity and convex sets

In this file we prove the following lemma, see `exists_continuous_forall_mem_convex_of_local`. Let
`X` be a normal paracompact topological space (e.g., any extended metric space). Let `E` be a
topological real vector space. Let `t : X → Set E` be a family of convex sets. Suppose that for each
point `x : X`, there exists a neighborhood `U ∈ 𝓝 X` and a function `g : X → E` that is continuous
on `U` and sends each `y ∈ U` to a point of `t y`. Then there exists a continuous map `g : C(X, E)`
such that `g x ∈ t x` for all `x`.

We also formulate a useful corollary, see `exists_continuous_forall_mem_convex_of_local_const`, that
assumes that local functions `g` are constants.

## Tags

partition of unity
-/


open Set Function

open Topology

variable {ι X E : Type*} [TopologicalSpace X] [AddCommGroup E] [Module ℝ E]

theorem PartitionOfUnity.finsum_smul_mem_convex {s : Set X} (f : PartitionOfUnity ι X s)
    {g : ι → X → E} {t : Set E} {x : X} (hx : x ∈ s) (hg : ∀ i, f i x ≠ 0 → g i x ∈ t)
    (ht : Convex ℝ t) : (∑ᶠ i, f i x • g i x) ∈ t :=
  ht.finsum_mem (fun _ => f.nonneg _ _) (f.sum_eq_one hx) hg
#align partition_of_unity.finsum_smul_mem_convex PartitionOfUnity.finsum_smul_mem_convex

variable [NormalSpace X] [ParacompactSpace X] [TopologicalSpace E] [ContinuousAdd E]
  [ContinuousSMul ℝ E] {t : X → Set E}

/-- Let `X` be a normal paracompact topological space (e.g., any extended metric space). Let `E` be
a topological real vector space. Let `t : X → Set E` be a family of convex sets. Suppose that for
each point `x : X`, there exists a neighborhood `U ∈ 𝓝 X` and a function `g : X → E` that is
continuous on `U` and sends each `y ∈ U` to a point of `t y`. Then there exists a continuous map
`g : C(X, E)` such that `g x ∈ t x` for all `x`. See also
`exists_continuous_forall_mem_convex_of_local_const`. -/
theorem exists_continuous_forall_mem_convex_of_local (ht : ∀ x, Convex ℝ (t x))
    (H : ∀ x : X, ∃ U ∈ 𝓝 x, ∃ g : X → E, ContinuousOn g U ∧ ∀ y ∈ U, g y ∈ t y) :
    ∃ g : C(X, E), ∀ x, g x ∈ t x := by
  choose U hU g hgc hgt using H
  obtain ⟨f, hf⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ (fun x => interior (U x))
    (fun x => isOpen_interior) fun x _ => mem_iUnion.2 ⟨x, mem_interior_iff_mem_nhds.2 (hU x)⟩
  refine ⟨⟨fun x => ∑ᶠ i, f i x • g i x,
    hf.continuous_finsum_smul (fun i => isOpen_interior) fun i => (hgc i).mono interior_subset⟩,
    fun x => f.finsum_smul_mem_convex (mem_univ x) (fun i hi => hgt _ _ ?_) (ht _)⟩
  exact interior_subset (hf _ <| subset_closure hi)
#align exists_continuous_forall_mem_convex_of_local exists_continuous_forall_mem_convex_of_local

/-- Let `X` be a normal paracompact topological space (e.g., any extended metric space). Let `E` be
a topological real vector space. Let `t : X → Set E` be a family of convex sets. Suppose that for
each point `x : X`, there exists a vector `c : E` that belongs to `t y` for all `y` in a
neighborhood of `x`. Then there exists a continuous map `g : C(X, E)` such that `g x ∈ t x` for all
`x`. See also `exists_continuous_forall_mem_convex_of_local`. -/
theorem exists_continuous_forall_mem_convex_of_local_const (ht : ∀ x, Convex ℝ (t x))
    (H : ∀ x : X, ∃ c : E, ∀ᶠ y in 𝓝 x, c ∈ t y) : ∃ g : C(X, E), ∀ x, g x ∈ t x :=
  exists_continuous_forall_mem_convex_of_local ht fun x =>
    let ⟨c, hc⟩ := H x
    ⟨_, hc, fun _ => c, continuousOn_const, fun _ => id⟩
#align exists_continuous_forall_mem_convex_of_local_const exists_continuous_forall_mem_convex_of_local_const
