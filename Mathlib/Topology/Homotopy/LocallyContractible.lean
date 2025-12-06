/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Topology.Homotopy.Contractible
public import Mathlib.Topology.Homotopy.Basic
public import Mathlib.Topology.Connected.LocPathConnected
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Strongly locally contractible spaces

This file defines `LocallyContractibleSpace` and `StronglyLocallyContractibleSpace`.

## Main definitions

* `LocallyContractibleSpace X`: classical local contractibility (null-homotopic inclusions).
* `StronglyLocallyContractibleSpace X`: a space where each point has a neighborhood basis
  consisting of contractible sets (not necessarily open).

## Main results

* `StronglyLocallyContractibleSpace.locallyContractible`: SLC implies classical LC
* `instLocPathConnectedSpace`: strongly locally contractible spaces are locally path-connected
* `StronglyLocallyContractibleSpace.of_bases`: a helper to construct strongly locally contractible
  spaces from a neighborhood basis
* `contractible_subset_basis`: basis of contractible neighborhoods contained in an open set
* `IsOpenEmbedding.stronglyLocallyContractibleSpace`: open embeddings preserve strong local
  contractibility
* `IsOpen.stronglyLocallyContractibleSpace`: open subsets of strongly locally contractible spaces
  are strongly locally contractible

## TODO

* Define contractible components and prove they are open in strongly locally contractible spaces
* Add examples: convex sets, real vector spaces, star-shaped sets
* Products of strongly locally contractible spaces

## Notes

**Terminology:** The classical definition of *locally contractible* (LC) requires that for every
point `x` and neighborhood `U ∋ x`, there exists a neighborhood `V ∋ x` with `V ⊆ U` such that the
inclusion `V ↪ U` is null-homotopic. The definition here is **strictly stronger**: we require
contractible neighborhoods to form a neighborhood basis. This is often called **strongly locally
contractible** (SLC).

**Hierarchy of notions:**
* "Basis of open contractible neighborhoods" (strongest)
* "Basis of contractible neighborhoods" (this file, SLC)
* "Null-homotopic inclusions" (classical LC, weakest)

This naming is not used uniformly: according to https://ncatlab.org/nlab/show/locally+contractible+space
the second and third notion here could also be called
"locally contractible" and "semilocally contractible" respectively.
We've enquired at
https://math.stackexchange.com/questions/5109428/terminology-for-local-contractibility-locally-contractible-vs-strongly-local
in the hope of getting definitive naming advice.

The Borsuk-Mazurkiewicz counterexample [borsuk_mazurkiewicz1934] shows that classical LC does not
imply SLC. Moreover, from a contractible neighborhood `S` one generally cannot shrink to an open
`V ⊆ S` that remains contractible, so requiring neighborhoods to be open is potentially strictly
stronger than SLC.
-/

@[expose] public section

noncomputable section

open Topology Filter Set Function ContinuousMap

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {x y : X} {ι : Type*}

section LocallyContractible

/-- Classical **local contractibility**: for every point and every neighborhood U,
there exists a neighborhood V ⊆ U such that the inclusion V ↪ U is null-homotopic.

This is weaker than `StronglyLocallyContractibleSpace`. -/
def LocallyContractibleSpace (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ (x : X) (U : Set X), U ∈ 𝓝 x →
    ∃ (V : Set X) (hVU : V ⊆ U), V ∈ 𝓝 x ∧ Nullhomotopic (inclusion hVU)

end LocallyContractible

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

/-- In a strongly locally contractible space, for any open set `U` containing `x`, there is a basis
of contractible neighborhoods of `x` contained in `U`. -/
theorem contractible_subset_basis {U : Set X} (h : IsOpen U) (hx : x ∈ U) :
    (𝓝 x).HasBasis (fun s : Set X => s ∈ 𝓝 x ∧ ContractibleSpace s ∧ s ⊆ U) id :=
  (contractible_basis x).hasBasis_self_subset (IsOpen.mem_nhds h hx)

/-- Strongly locally contractible spaces are locally path-connected. -/
instance (priority := 100) instLocPathConnectedSpace : LocPathConnectedSpace X where
  path_connected_basis x := by
    refine contractible_basis x |>.to_hasBasis' (fun s ⟨hs, hs'⟩ ↦ ⟨s, ⟨hs, ?_⟩, le_rfl⟩)
      (fun s hs ↦ hs.1)
    rw [isPathConnected_iff_pathConnectedSpace]
    infer_instance

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

section Implications

/-- The strong notion (contractible neighborhood basis)
implies the classical notion (null-homotopic inclusions).
The converse is false by the Borsuk-Mazurkiewicz counterexample [borsuk_mazurkiewicz1934];
see also [MO88628] for discussion and the Whitehead manifold example. -/
theorem StronglyLocallyContractibleSpace.locallyContractible [StronglyLocallyContractibleSpace X] :
    LocallyContractibleSpace X := by
  intro x U hU
  obtain ⟨V, ⟨hVmem, hVcontractible⟩, hVU⟩ := (contractible_basis x).mem_iff.mp hU
  refine ⟨V, hVU, hVmem, ?_⟩
  -- V is contractible, so the identity on V is nullhomotopic to a constant map
  obtain ⟨v₀, hid⟩ := id_nullhomotopic V
  -- The inclusion V ↪ U is homotopic to the constant map at (inclusion v₀)
  refine ⟨ContinuousMap.inclusion hVU v₀, ?_⟩
  convert Homotopic.comp (.refl _) hid
  ext
  simp

end Implications
