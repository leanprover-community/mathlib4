/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Topology.Connected.LocPathConnected

/-!
# Locally contractible spaces

This file defines `LocallyContractibleSpace`, a predicate class asserting that a topological space
is locally contractible, in that each point has a basis of contractible neighborhoods.

## Main definitions

* `LocallyContractibleSpace X`: a space where each point has a neighborhood basis consisting of
  contractible sets.

## Main results

* `instLocPathConnectedSpace`: locally contractible spaces are locally path-connected
* `LocallyContractibleSpace.of_bases`: a helper to construct locally contractible spaces from a
  neighborhood basis
* `contractible_subset_basis`: basis of contractible neighborhoods contained in an open set
* `IsOpenEmbedding.locallyContractibleSpace`: open embeddings preserve local contractibility (sorry)
* `IsOpen.locallyContractibleSpace`: open subsets of locally contractible spaces are locally
  contractible

## TODO

* Prove `IsOpenEmbedding.locallyContractibleSpace` without sorry (needs lemma relating
  contractibility under homeomorphisms of subspaces)
* Define contractible components and prove they are open in locally contractible spaces
* Show that contractible neighborhoods can be required to be open
* Add examples: convex sets, real vector spaces, manifolds
* Quotients and products of locally contractible spaces
-/

noncomputable section

open Topology Filter Set Function

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {x y : X} {ι : Type*}

section LocallyContractibleSpace

/-- A topological space is locally contractible if, at every point, contractible
neighborhoods form a neighborhood basis. -/
class LocallyContractibleSpace (X : Type*) [TopologicalSpace X] : Prop where
  /-- Each neighborhood filter has a basis of contractible neighborhoods. -/
  contractible_basis : ∀ x : X,
    (𝓝 x).HasBasis (fun s : Set X => s ∈ 𝓝 x ∧ ContractibleSpace s) id

export LocallyContractibleSpace (contractible_basis)

theorem LocallyContractibleSpace.of_bases {p : X → ι → Prop} {s : X → ι → Set X}
    (h : ∀ x, (𝓝 x).HasBasis (p x) (s x)) (h' : ∀ x i, p x i → ContractibleSpace (s x i)) :
    LocallyContractibleSpace X where
  contractible_basis x := by
    rw [hasBasis_self]
    intro t ht
    obtain ⟨i, hpi, hi⟩ := (h x).mem_iff.mp ht
    exact ⟨s x i, (h x).mem_of_mem hpi, h' x i hpi, hi⟩

variable [LocallyContractibleSpace X]

/-- Contractible neighborhoods form a basis, so path-connected neighborhoods also form a basis. -/
theorem contractible_subset_basis {U : Set X} (h : IsOpen U) (hx : x ∈ U) :
    (𝓝 x).HasBasis (fun s : Set X => s ∈ 𝓝 x ∧ ContractibleSpace s ∧ s ⊆ U) id :=
  (contractible_basis x).hasBasis_self_subset (IsOpen.mem_nhds h hx)

/-- Locally contractible spaces are locally path-connected. -/
instance (priority := 100) instLocPathConnectedSpace : LocPathConnectedSpace X := by
  constructor
  intro x
  have := contractible_basis x
  refine ⟨fun t => ?_⟩
  constructor
  · intro ht
    obtain ⟨s, hs, hst⟩ := this.mem_iff.mp ht
    use s, ⟨hs.1, ?_⟩, hst
    rw [isPathConnected_iff_pathConnectedSpace]
    haveI := hs.2
    infer_instance
  intro ⟨s, hs, hst⟩
  exact mem_of_superset hs.1 hst

theorem Topology.IsOpenEmbedding.locallyContractibleSpace {e : Y → X} (he : IsOpenEmbedding e) :
    LocallyContractibleSpace Y := by
  have (y : Y) :
      (𝓝 y).HasBasis (fun s ↦ s ∈ 𝓝 (e y) ∧ ContractibleSpace s ∧ s ⊆ range e) (e ⁻¹' ·) :=
    he.basis_nhds <| contractible_subset_basis he.isOpen_range (mem_range_self _)
  refine .of_bases this fun y s ⟨_, hs, hse⟩ ↦ ?_
  -- The restriction of `e` to `e ⁻¹' s` gives a homeomorphism onto `s`
  -- since `e` is an open embedding and `s ⊆ range e`.
  -- Therefore contractibility is preserved.
  sorry

theorem IsOpen.locallyContractibleSpace {U : Set X} (h : IsOpen U) :
    LocallyContractibleSpace U :=
  h.isOpenEmbedding_subtypeVal.locallyContractibleSpace

end LocallyContractibleSpace
