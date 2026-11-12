/-
Copyright (c) 2026 Thomas Browning, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Bhavik Mehta
-/
module

public import Mathlib.Combinatorics.Hypergraph.Basic
public import Mathlib.Data.Finset.Density
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Data.Set.Card

/-!
# Combinatorial Designs

This file defines incidence systems and combinatorial designs.

An incidence system consists of a carrier set and subsets called blocks. We index our blocks
by a subset of an indexing type to make it easy to add and remove blocks if desired.
Duplicate blocks are permitted unless `IncidenceSystem.IsSimple` is imposed.

Note the similarity with `Hypergraph` which consists of a carrier set and subsets called sets.
The primary difference is that `Hypergraph` edges are not indexed and do not allow for duplication.

## Main definitions

* `IncidenceSystem`: An incidence system consists of a carrier set and subsets called blocks.
* `IncidenceSystem.IsSimple`: An incidence system is simple if there are no duplicate blocks.
* `IncidenceSystem.IsUniform`: An incidence system is `k`-uniform if every block has size `k`.
* `IncidenceSystem.IsBalanced`
* `IncidenceSystem.IsDesign`
* `IncidenceSystem.IsSteiner`

## Main statements

* `fooBar_unique`

## Implementation details

We place everything in the `IncidenceSystem` namespace, because this still allows one to write
`{α β : Type*} (d : Design α β) [d.IsSimple] [d.IsUniform]`.

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
  block_subset {b} (hb : b ∈ blockSet) : block b ⊆ carrier := by grind

initialize_simps_projections IncidenceSystem (as_prefix carrier, as_prefix blockSet,
  as_prefix block)

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

/-- The indiscrete incidence system consists of the carrier as a single block. -/
@[simps]
def indiscrete (s : Set α) (b : β) : IncidenceSystem α β where
  carrier := s
  blockSet := {b}
  block _ := s

/-- An incidence system is simple if there are no duplicate blocks. -/
@[mk_iff]
class IsSimple (d : IncidenceSystem α β) : Prop where
  block_injOn_blockSet : d.blockSet.InjOn d.block := by simp

@[simp, grind .]
protected theorem IsSimple.ofHypergraph (H : Hypergraph α) : (ofHypergraph H).IsSimple where

@[simp, grind .]
protected theorem IsSimple.discrete (s : Set α) : (discrete s).IsSimple where

@[simp, grind .]
protected theorem IsSimple.indiscrete (s : Set α) (b : β) : (indiscrete s b).IsSimple where

/-- An incidence system is `k`-uniform if every block has size `k`. -/
@[mk_iff]
structure IsUniform (d : IncidenceSystem α β) (k : ℕ) : Prop where
  uniform {b} (hb : b ∈ d.blockSet) : (d.block b).ncard = k

attribute [grind .] IsUniform.uniform

@[simp, grind .]
protected theorem IsUniform.discrete (s : Set α) : (discrete s).IsUniform 1 where
  uniform {x} _ := by simp

@[simp, grind .]
protected theorem IsUniform.indiscrete (s : Set α) (b : β) :
    (indiscrete s b).IsUniform s.ncard where
  uniform _ := by simp

theorem IsUniform.nonempty_block {d : IncidenceSystem α β}
    {k : ℕ} (hd : d.IsUniform k) (hk : k ≠ 0) {b : β} (hb : b ∈ d.blockSet) :
    (d.block b).Nonempty := by
  grind [Set.nonempty_of_ncard_ne_zero]

theorem IsUniform.finite_block {d : IncidenceSystem α β}
    {k : ℕ} (hd : d.IsUniform k) (hk : k ≠ 0) {b : β} (hb : b ∈ d.blockSet) :
    (d.block b).Finite := by
  grind [Set.finite_of_ncard_ne_zero]

@[mk_iff]
structure IsBalanced (d : IncidenceSystem α β) (t l : ℕ) where
  balanced (s : Set α) (hs : s ⊆ d.carrier) (hs : s.ncard = t) :
    {b ∈ d.blockSet | s ⊆ d.block b}.ncard = l

@[mk_iff]
structure IsDesign (d : IncidenceSystem α β) (t n k l : ℕ) extends
    d.IsUniform k, d.IsBalanced t l where
  card_carrier : d.carrier.ncard = n

attribute [grind .] IsDesign.card_carrier

theorem IsDesign.nonempty {d : IncidenceSystem α β}
    {t n k l : ℕ} (hd : d.IsDesign t n k l) (hk : n ≠ 0) :
    d.carrier.Nonempty := by
  grind [Set.nonempty_of_ncard_ne_zero]

theorem IsDesign.finite {d : IncidenceSystem α β}
    {t n k l : ℕ} (hd : d.IsDesign t n k l) (hk : n ≠ 0) :
    d.carrier.Finite := by
  grind [Set.finite_of_ncard_ne_zero]

def IsSteiner (d : IncidenceSystem α β) (t k n : ℕ) := d.IsDesign t n k 1

theorem _root_.Set.subsingleton_of_ncard_eq_one {s : Set α} (hs : s.ncard = 1) : s.Subsingleton := by
  have : Finite s := Set.finite_of_ncard_pos (by grind)
  rw [← Set.ncard_le_one_iff_subsingleton, hs]

theorem IsSteiner.isSimple {d : IncidenceSystem α β} {t k n : ℕ} (hd : d.IsSteiner t k n)
    (htk : t ≤ k) : d.IsSimple where
  block_injOn_blockSet b₁ hb₁ b₂ hb₂ h := by
    obtain ⟨s, hs, hst⟩ := Set.exists_subset_card_eq (htk.trans (hd.uniform hb₁).ge)
    exact Set.subsingleton_of_ncard_eq_one
      (hd.balanced s (hs.trans (d.block_subset hb₁)) hst) ⟨hb₁, hs⟩ ⟨hb₂, hs.trans_eq h⟩

end IncidenceSystem
