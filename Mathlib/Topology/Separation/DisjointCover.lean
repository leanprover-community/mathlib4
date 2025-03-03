/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import Mathlib.Order.Disjointed
import Mathlib.Topology.Separation.Profinite
import Mathlib.Topology.Sets.Closeds
import Mathlib.Topology.Sets.OpenCover

/-!
# Disjoint covers of profinite spaces

We show that if `X` is a profinite space, then any open covering of `X` can be refined to a finite
covering by disjoint nonempty clopens.
-/

open Set

open scoped Function Finset

namespace TopologicalSpace.IsOpenCover

variable {ι X : Type*}
  [TopologicalSpace X] [TotallyDisconnectedSpace X] [T2Space X] [CompactSpace X] {U : ι → Opens X}

/-- Any open cover of a profinite space can be refined to a finite cover by clopens. -/
lemma exists_finite_clopen_cover (hU : IsOpenCover U) : ∃ (n : ℕ) (V : Fin n → Clopens X),
    (∀ j, ∃ i, (V j : Set X) ⊆ U i) ∧ univ ⊆ ⋃ j, (V j : Set X) := by
  -- Choose an index `r x` for each point in `X` such that `∀ x, x ∈ U (r x)`.
  choose r hr using hU.exists_mem
  -- Choose a clopen neighbourhood `V x` of each `x` contained in `U (r x)`.
  choose V hV hVx hVU using fun x ↦ compact_exists_isClopen_in_isOpen (U _).isOpen (hr x)
  -- Apply compactness to extract a finite subset of the `V`s which covers `X`.
  obtain ⟨t, ht⟩ : ∃ t, univ ⊆ ⋃ i ∈ t, V i :=
    isCompact_univ.elim_finite_subcover V (fun x ↦ (hV x).2) (fun x _ ↦ mem_iUnion.mpr ⟨x, hVx x⟩)
  -- Biject it noncanonically with `Fin n` for some `n`.
  refine ⟨_, fun j ↦ ⟨_, hV (t.equivFin.symm j)⟩, fun j ↦ ⟨_, hVU _⟩, fun x hx ↦ ?_⟩
  obtain ⟨m, hm, hm'⟩ := mem_iUnion₂.mp (ht hx)
  exact Set.mem_iUnion_of_mem (t.equivFin ⟨m, hm⟩) (by simpa)

/-- Any open cover of a profinite space can be refined to a finite cover by pairwise disjoint
nonempty clopens. -/
lemma exists_finite_nonempty_disjoint_clopen_cover (hU : IsOpenCover U) :
    ∃ (n : ℕ) (W : Fin n → Clopens X), (∀ j, W j ≠ ⊥ ∧ ∃ i, (W j : Set X) ⊆ U i)
    ∧ (univ : Set X) ⊆ ⋃ j, ↑(W j) ∧ Pairwise (Disjoint on W) := by
  classical
  obtain ⟨n, V, hVle, hVun⟩ := hU.exists_finite_clopen_cover
  obtain ⟨W, hWle, hWun, hWd⟩ := Fintype.exists_disjointed_le V
  simp only [← SetLike.coe_set_eq, Clopens.coe_finset_sup, Finset.mem_univ, iUnion_true] at hWun
  let t : Finset (Fin n) := {j | W j ≠ ⊥}
  refine ⟨#t, fun k ↦ W (t.equivFin.symm k), fun k ↦ ⟨?_, ?_⟩, fun x hx ↦ ?_, ?_⟩
  · exact (Finset.mem_filter.mp (t.equivFin.symm k).2).2
  · exact match hVle (t.equivFin.symm k) with | ⟨i, hi⟩ => ⟨i, subset_trans (hWle _) hi⟩
  · obtain ⟨j, hj⟩ := mem_iUnion.mp <| (hWun ▸ hVun) hx
    have : W j ≠ ⊥ := by simpa [← SetLike.coe_ne_coe, ← Set.nonempty_iff_ne_empty] using ⟨x, hj⟩
    exact mem_iUnion.mpr ⟨t.equivFin ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, this⟩⟩, by simpa⟩
  · exact hWd.comp_of_injective <| Subtype.val_injective.comp t.equivFin.symm.injective

end TopologicalSpace.IsOpenCover
