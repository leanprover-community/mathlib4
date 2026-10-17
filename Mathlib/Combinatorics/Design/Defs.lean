/-
Copyright (c) 2026 Thomas Browning, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Bhavik Mehta
-/
module

public import Mathlib.Combinatorics.Hypergraph.Basic

/-!
# Combinatorial Designs

This file defines incidence systems and combinatorial designs.

## Main definitions

* `IncidenceSystem`: An incidence system consists of a carrier set and subsets called blocks.
* `IncidenceSystem.IsSimple`: An incidence system is simple if there are no duplicate blocks.
* `IncidenceSystem.IsUniform`: An incidence system is `k`-uniform if every block has size `k`.

## Implementation details

We place everything in the `IncidenceSystem` namespace, because this still allows one to write
`{α β : Type*} (d : Design α β) [d.IsSimple] [d.IsUniform]`.

We index our blocks by a subset of an indexing type `β` to make it easy to add and remove blocks
if desired. Duplicate blocks are permitted unless `IncidenceSystem.IsSimple` is imposed.

## TODO

* Define regular (number of blocks containing a given point is fixed)
* Define equidistance (pairwise intersections have a given size)
-/


@[expose] public section

variable (α β : Type*)

/-- An incidence system consists of a carrier set and subsets called blocks. We index our blocks
by a subset of an indexing type `β` to make it easy to add and remove blocks if desired.
Duplicate blocks are permitted unless `IncidenceSystem.IsSimple` is imposed. -/
structure IncidenceSystem where
  /-- The ambient set for the incidence system. -/
  carrier : Set α
  /-- The indexing set for the blocks. -/
  blockSet : Set β
  /-- The function from the indexing type `β` to the blocks in `α`. -/
  block (b : β) : Set α
  /-- The blocks must be subsets of the ambient set. -/
  block_subset {b} (hb : b ∈ blockSet) : block b ⊆ carrier

attribute [grind →] IncidenceSystem.block_subset

namespace IncidenceSystem

variable {α β}

theorem biUnion_block_subset (d : IncidenceSystem α β) :
    ⋃ b ∈ d.blockSet, d.block b ⊆ d.carrier :=
  Set.iUnion₂_subset @d.block_subset

theorem mem_of_mem_block (d : IncidenceSystem α β) {b : β} {x : α} (hx : x ∈ d.block b)
    (hb : b ∈ d.blockSet) : x ∈ d.carrier := by
  grind

/-- Every hypergraph can be viewed as an incidence system where the hyperedges become the blocks. -/
@[simps]
def ofHypergraph (H : Hypergraph α) : IncidenceSystem α (Set α) where
  carrier := H.vertexSet
  blockSet := H.edgeSet
  block x := x
  block_subset := H.subset_vertexSet_of_mem_edgeSet

/-- Every incidence system can be viewed as a hypergraph where the blocks become the hyperedges.
Note that hypergraphs are simple in mathlib, so this function will collapse duplicate blocks. -/
@[simps]
def toHypergraph (d : IncidenceSystem α β) : Hypergraph α where
  vertexSet := d.carrier
  edgeSet := d.block '' d.blockSet
  subset_vertexSet_of_mem_edgeSet' := by grind

@[simp]
theorem toHypergraph_ofHypergraph (H : Hypergraph α) : (ofHypergraph H).toHypergraph = H := by
  simp [Hypergraph.ext_iff]

/-- The discrete incidence system consists of singleton blocks. -/
@[simps]
def discrete (s : Set α) : IncidenceSystem α α where
  carrier := s
  blockSet := s
  block x := {x}
  block_subset := Set.singleton_subset_iff.mpr

/-- The indiscrete incidence system consists of the carrier as a single block. -/
@[simps]
def indiscrete (s : Set α) (b : β) : IncidenceSystem α β where
  carrier := s
  blockSet := {b}
  block _ := s
  block_subset _ := subset_rfl

/-- An incidence system is simple if there are no duplicate blocks. -/
@[mk_iff]
class IsSimple (d : IncidenceSystem α β) : Prop where
  injOn : d.blockSet.InjOn d.block

theorem isSimple_ofHypergraph (H : Hypergraph α) : (ofHypergraph H).IsSimple where
  injOn := by simp

theorem isSimple_discrete (s : Set α) : (discrete s).IsSimple where
  injOn := by simp

theorem isSimple_indiscrete (s : Set α) (b : β) : (indiscrete s b).IsSimple where
  injOn := by simp

/-- An incidence system is `k`-uniform if every block has size `k`. -/
@[mk_iff]
structure IsUniform (d : IncidenceSystem α β) (k : ℕ) : Prop where
  uniform {b} (hb : b ∈ d.blockSet) : (d.block b).ncard = k

attribute [grind .] IsUniform.uniform

theorem isUniform_discrete (s : Set α) : (discrete s).IsUniform 1 where
  uniform {x} _ := by simp

theorem isUniform_indiscrete (s : Set α) (b : β) : (indiscrete s b).IsUniform s.ncard where
  uniform _ := by simp

theorem IsUniform.nonempty_block {d : IncidenceSystem α β}
    {k : ℕ} (hd : d.IsUniform k) (hk : k ≠ 0) {b : β} (hb : b ∈ d.blockSet) :
    (d.block b).Nonempty := by
  grind [Set.nonempty_of_ncard_ne_zero]

theorem IsUniform.finite_block {d : IncidenceSystem α β}
    {k : ℕ} (hd : d.IsUniform k) (hk : k ≠ 0) {b : β} (hb : b ∈ d.blockSet) :
    (d.block b).Finite := by
  grind [Set.finite_of_ncard_ne_zero]

end IncidenceSystem
