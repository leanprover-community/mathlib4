/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Set.Disjoint
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Set.Lattice
import Mathlib.Init
import Mathlib.Order.Filter.Finite
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Closure
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Neighborhoods

/-!
# Infinite Hausdorff topological spaces

In this file we prove several properties of infinite Hausdorff topological spaces.

- `exists_seq_infinite_isOpen_pairwise_disjoint`: there exists a sequence
  of pairwise disjoint infinite open sets;
- `exists_topology_isEmbedding_nat`: there exists a topological embedding of `ℕ` into the space;
- `exists_infinite_discreteTopology`: there exists an infinite subset with discrete topology.
-/

public section

open Function Filter Set Topology

variable (X : Type*) [TopologicalSpace X] [T2Space X] [Infinite X]

/-- In an infinite Hausdorff topological space, there exists a sequence of pairwise disjoint
infinite open sets. -/
theorem exists_seq_infinite_isOpen_pairwise_disjoint :
    ∃ U : ℕ → Set X, (∀ n, (U n).Infinite) ∧ (∀ n, IsOpen (U n)) ∧ Pairwise (Disjoint on U) := by
  suffices ∃ U : ℕ → Set X, (∀ n, (U n).Nonempty) ∧ (∀ n, IsOpen (U n)) ∧
      Pairwise (Disjoint on U) by
    rcases this with ⟨U, hne, ho, hd⟩
    refine ⟨fun n ↦ ⋃ m, U (.pair n m), ?_, fun _ ↦ isOpen_iUnion fun _ ↦ ho _, ?_⟩
    · refine fun n ↦ infinite_iUnion fun i j hij ↦ ?_
      suffices n.pair i = n.pair j by simpa
      apply hd.eq
      simpa [hij, onFun] using (hne _).ne_empty
    · refine fun n n' hne ↦ disjoint_iUnion_left.2 fun m ↦ disjoint_iUnion_right.2 fun m' ↦ hd ?_
      simp [hne]
  by_cases h : DiscreteTopology X
  · refine ⟨fun n ↦ {Infinite.natEmbedding X n}, fun _ ↦ singleton_nonempty _,
      fun _ ↦ isOpen_discrete _, fun _ _ h ↦ ?_⟩
    simpa using h
  · simp only [discreteTopology_iff_nhds_ne, not_forall, ← ne_eq, ← neBot_iff] at h
    rcases h with ⟨x, hx⟩
    suffices ∃ U : ℕ → Set X, (∀ n, (U n).Nonempty ∧ IsOpen (U n) ∧ (U n)ᶜ ∈ 𝓝 x) ∧
        Pairwise (Disjoint on U) by
      rcases this with ⟨U, hU, hd⟩
      exact ⟨U, fun n ↦ (hU n).1, fun n ↦ (hU n).2.1, hd⟩
    have : Std.Symm (α := Set X) Disjoint := ⟨fun _ _ h ↦ h.symm⟩
    refine exists_seq_of_forall_finset_exists' (fun U : Set X ↦ U.Nonempty ∧ IsOpen U ∧ Uᶜ ∈ 𝓝 x)
      Disjoint fun S hS ↦ ?_
    have : (⋂ U ∈ S, interior (Uᶜ)) \ {x} ∈ 𝓝[≠] x := inter_mem_inf ((biInter_finset_mem _).2
      fun U hU ↦ interior_mem_nhds.2 (hS _ hU).2.2) (mem_principal_self _)
    rcases hx.nonempty_of_mem this with ⟨y, hyU, hyx : y ≠ x⟩
    rcases t2_separation hyx with ⟨V, W, hVo, hWo, hyV, hxW, hVW⟩
    refine ⟨V ∩ ⋂ U ∈ S, interior (Uᶜ), ⟨⟨y, hyV, hyU⟩, ?_, ?_⟩, fun U hU ↦ ?_⟩
    · exact hVo.inter (isOpen_biInter_finset fun _ _ ↦ isOpen_interior)
    · refine mem_of_superset (hWo.mem_nhds hxW) fun z hzW ⟨hzV, _⟩ ↦ ?_
      exact disjoint_left.1 hVW hzV hzW
    · exact disjoint_left.2 fun z hzU ⟨_, hzU'⟩ ↦ interior_subset (mem_iInter₂.1 hzU' U hU) hzU

/-- If `X` is an infinite Hausdorff topological space, then there exists a topological embedding
`f : ℕ → X`.

Note: this theorem is true for an infinite KC-space but the proof in that case is different. -/
theorem exists_topology_isEmbedding_nat : ∃ f : ℕ → X, IsEmbedding f := by
  rcases exists_seq_infinite_isOpen_pairwise_disjoint X with ⟨U, hUi, hUo, hd⟩
  choose f hf using fun n ↦ (hUi n).nonempty
  refine ⟨f, IsInducing.isEmbedding ⟨Eq.symm (eq_bot_of_singletons_open fun n ↦ ⟨U n, hUo n, ?_⟩)⟩⟩
  refine eq_singleton_iff_unique_mem.2 ⟨hf _, fun m hm ↦ ?_⟩
  exact hd.eq (not_disjoint_iff.2 ⟨f m, hf _, hm⟩)

/-- If `X` is an infinite Hausdorff topological space, then there exists an infinite set `s : Set X`
that has the induced topology is the discrete topology. -/
theorem exists_infinite_discreteTopology : ∃ s : Set X, s.Infinite ∧ DiscreteTopology s := by
  rcases exists_topology_isEmbedding_nat X with ⟨f, hf⟩
  refine ⟨range f, infinite_range_of_injective hf.injective, ?_⟩
  exact hf.toHomeomorph.symm.isEmbedding.discreteTopology
