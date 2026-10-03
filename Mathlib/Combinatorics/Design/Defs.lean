/-
Copyright (c) 2026 Thomas Browning, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Bhavik Mehta
-/
module

public import Mathlib.Combinatorics.Hypergraph.Basic
public import Mathlib.Data.Finset.Density
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Data.Set.Card

/-!
# Combinatorial Designs

This file defines combinatorial designs.

## Main definitions

* `IncidenceSystem`
* `IncidenceSystem.IsSimple`
* `IncidenceSystem.IsUniform`
* `IncidenceSystem.IsBalanced`
* `IncidenceSystem.IsDesign`
* `IncidenceSystem.IsSteiner`

## Main statements

* `fooBar_unique`

## Implementation details

We place everything in the `IncidenceSystem` namespace, but this still allows for
`{α β : Type*} (d : Design α β) [d.IsSimple] [d.IsUniform]`.

## References

* [F. Bar, *Quuxes*][bibkey]

## TODO

* Define regular (number of blocks containing a given point is fixed)
* Define equidistance (pairwise intersections have a given size)

## Tags

Foobars, barfoos
-/


@[expose] public section

variable (α β : Type*)

/-- A combinatorial design consists of a carrier set and subsets called blocks. We index our blocks
by a subset of an indexing type `β` to make it easy to add and remove blocks if desired.
Duplicate blocks are permitted unless `IncidenceSystem.IsSimple` is imposed. -/
structure IncidenceSystem where
  carrier : Set α
  blockSet : Set β
  block (b : β) : Set α
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

/-- An incidence system is `k`-uniform if every block has cardinality `k`. -/
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

--------------------------------------------- CUT

-- todo: find better letter for `Λ`
@[mk_iff]
structure IsBalanced (d : IncidenceSystem α β) (t Λ : ℕ) where
  balanced (s : Set α) (hs : s ⊆ d.carrier) (hs : s.ncard = t) :
    {b ∈ d.blockSet | s ⊆ d.block b}.ncard = Λ

@[mk_iff]
structure IsDesign (d : IncidenceSystem α β) (t n k Λ : ℕ) extends
    d.IsUniform k, d.IsBalanced t Λ where
  card_carrier : d.carrier.ncard = n

attribute [grind .] IsDesign.card_carrier

theorem IsDesign.nonempty {d : IncidenceSystem α β}
    {t n k Λ : ℕ} (hd : d.IsDesign t n k Λ) (hk : n ≠ 0) :
    d.carrier.Nonempty := by
  grind [Set.nonempty_of_ncard_ne_zero]

theorem IsDesign.finite {d : IncidenceSystem α β}
    {t n k Λ : ℕ} (hd : d.IsDesign t n k Λ) (hk : n ≠ 0) :
    d.carrier.Finite := by
  grind [Set.finite_of_ncard_ne_zero]

def IsSteiner (d : IncidenceSystem α β) (t k n : ℕ) := d.IsDesign t n k 1

-- PRed
theorem _root_.Set.subsingleton_of_ncard_eq_one {s : Set α} (hs : s.ncard = 1) : s.Subsingleton := by
  have : Finite s := Set.finite_of_ncard_pos (by grind)
  rw [← Set.ncard_le_one_iff_subsingleton, hs]

theorem IsSteiner.isSimple {d : IncidenceSystem α β} {t k n : ℕ} (hd : d.IsSteiner t k n)
    (htk : t ≤ k) : d.IsSimple where
  injOn b₁ hb₁ b₂ hb₂ h := by
    obtain ⟨s, hs, hst⟩ := Set.exists_subset_card_eq (htk.trans (hd.uniform hb₁).ge)
    exact Set.subsingleton_of_ncard_eq_one
      (hd.balanced s (hs.trans (d.block_subset hb₁)) hst) ⟨hb₁, hs⟩ ⟨hb₂, hs.trans_eq h⟩

end IncidenceSystem
