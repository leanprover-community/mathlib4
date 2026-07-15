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



TODO:
* Define regular (number of blocks containing a given point is fixed)
* Define equidistance (pairwise intersections have a given size)

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

## Tags

Foobars, barfoos
-/


@[expose] public section

variable (α β : Type*)

/-- A combinatorial design consists of a carrier -/
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

/-- docstring! -/
@[simps]
def ofHypergraph (H : Hypergraph α) : IncidenceSystem α (Set α) where
  carrier := H.vertexSet
  blockSet := H.edgeSet
  block x := x
  block_subset := H.subset_vertexSet_of_mem_edgeSet

/-- docstring! -/
@[simps]
def toHypergraph (d : IncidenceSystem α β) : Hypergraph α where
  vertexSet := d.carrier
  edgeSet := d.block '' d.blockSet
  subset_vertexSet_of_mem_edgeSet' := by grind

@[simp]
theorem toHypergraph_ofHypergraph (H : Hypergraph α) : (ofHypergraph H).toHypergraph = H := by
  simp [Hypergraph.ext_iff]

variable (α β)



variable {α β}

@[mk_iff]
class IsSimple (d : IncidenceSystem α β) : Prop where
  injOn : d.blockSet.InjOn d.block

@[mk_iff]
structure IsUniform (d : IncidenceSystem α β) (k : ℕ) : Prop where
  uniform {b} (hb : b ∈ d.blockSet) : (d.block b).ncard = k

attribute [grind .] IsUniform.uniform

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

-- `t ≤ n` implies `k ≤ n`?
theorem IsSteiner.isSimple {d : IncidenceSystem α β} {t k n : ℕ} (hd : d.IsSteiner t k n)
    (htn : t ≤ n) (hkn : k ≤ n) : d.IsSimple where
  injOn b₁ hb₁ b₂ hb₂ h := by
    sorry

end IncidenceSystem
