/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Topology.Connected.LocPathConnected
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Strongly locally contractible spaces

This file defines `StronglyLocallyContractibleSpace`, a predicate class asserting that a
topological space is strongly locally contractible, meaning each point has a neighborhood basis
consisting of contractible sets.

## Main definitions

* `StronglyLocallyContractibleSpace X`: a space where each point has a neighborhood basis
  consisting of contractible subspaces.

## Main results

* `instLocPathConnectedSpace`: strongly locally contractible spaces are locally path-connected
* `StronglyLocallyContractibleSpace.of_bases`: a helper to construct strongly locally contractible
  spaces from a neighborhood basis
* `contractible_subset_basis`: basis of contractible neighborhoods contained in an open set
* `IsOpenEmbedding.stronglyLocallyContractibleSpace`: open embeddings preserve strong local
  contractibility
* `IsOpen.stronglyLocallyContractibleSpace`: open subsets of strongly locally contractible spaces
  are strongly locally contractible

## TODO

* Define classical local contractibility (null-homotopic inclusions) and prove SLC implies LC
* Define contractible components and prove they are open in strongly locally contractible spaces
* Add examples: convex sets, real vector spaces, star-shaped sets
* Quotients and products of strongly locally contractible spaces

## Notes

**Terminology:** The classical definition of *locally contractible* (LC) requires that for every
point x and neighborhood U ∋ x, there exists a neighborhood V ∋ x with V ⊆ U such that the
inclusion V ↪ U is null-homotopic. The definition here is **strictly stronger**: we require
contractible neighborhoods to form a neighborhood basis. This is often called **strongly locally
contractible** (SLC).

**Hierarchy of notions:**
* "Basis of open contractible neighborhoods" (strongest)
* "Basis of contractible neighborhoods" (this file, SLC)
* "Null-homotopic inclusions" (classical LC, weakest)

The Borsuk-Mazurkiewicz counterexample (1934) shows that classical LC does not imply SLC. Moreover,
from a contractible neighborhood S one generally cannot shrink to an open V ⊆ S that remains
contractible, so requiring neighborhoods to be open is potentially strictly stronger than SLC.
-/

noncomputable section

open Topology Filter Set Function

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {x y : X} {ι : Type*}

section StronglyLocallyContractibleSpace

/-- A topological space is **strongly locally contractible** if, at every point, contractible
neighborhoods form a neighborhood basis. Here "contractible" means contractible as a subspace.

This is strictly stronger than the classical notion of locally contractible, which only requires
null-homotopic inclusions. -/
class StronglyLocallyContractibleSpace (X : Type*) [TopologicalSpace X] : Prop where
  /-- Each neighborhood filter has a basis of contractible subspace neighborhoods. -/
  contractible_basis : ∀ x : X,
    (𝓝 x).HasBasis (fun s : Set X => s ∈ 𝓝 x ∧ ContractibleSpace s) id

export StronglyLocallyContractibleSpace (contractible_basis)

/-- A helper to construct a strongly locally contractible space from a neighborhood basis where
each basis element is contractible as a subspace. -/
theorem StronglyLocallyContractibleSpace.of_bases {p : X → ι → Prop} {s : X → ι → Set X}
    (h : ∀ x, (𝓝 x).HasBasis (p x) (s x)) (h' : ∀ x i, p x i → ContractibleSpace (s x i)) :
    StronglyLocallyContractibleSpace X where
  contractible_basis x := by
    rw [hasBasis_self]
    intro t ht
    obtain ⟨i, hpi, hi⟩ := (h x).mem_iff.mp ht
    exact ⟨s x i, (h x).mem_of_mem hpi, h' x i hpi, hi⟩

variable [StronglyLocallyContractibleSpace X]

/-- In a strongly locally contractible space, for any open set U containing x, there is a basis of
contractible neighborhoods of x contained in U. -/
theorem contractible_subset_basis {U : Set X} (h : IsOpen U) (hx : x ∈ U) :
    (𝓝 x).HasBasis (fun s : Set X => s ∈ 𝓝 x ∧ ContractibleSpace s ∧ s ⊆ U) id :=
  (contractible_basis x).hasBasis_self_subset (IsOpen.mem_nhds h hx)

/-- Strongly locally contractible spaces are locally path-connected. -/
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

/-- Open embeddings preserve strong local contractibility: if `X` is strongly locally contractible
and `e : Y → X` is an open embedding, then `Y` is strongly locally contractible. -/
theorem Topology.IsOpenEmbedding.stronglyLocallyContractibleSpace {e : Y → X}
    (he : IsOpenEmbedding e) : StronglyLocallyContractibleSpace Y :=
  .of_bases (fun _ ↦ he.basis_nhds <| contractible_subset_basis he.isOpen_range (mem_range_self _))
    fun _ _ ⟨_, hs, hse⟩ ↦
      (he.toIsEmbedding.homeomorphOfSubsetRange hse).contractibleSpace_iff.mpr hs

/-- Open subsets of strongly locally contractible spaces are strongly locally contractible. -/
theorem IsOpen.stronglyLocallyContractibleSpace {U : Set X} (h : IsOpen U) :
    StronglyLocallyContractibleSpace U :=
  h.isOpenEmbedding_subtypeVal.stronglyLocallyContractibleSpace

end StronglyLocallyContractibleSpace
