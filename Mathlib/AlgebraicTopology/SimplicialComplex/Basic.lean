/-
Copyright (c) 2025 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.Independent

/-!
# Abstract Simplicial complexes

In this file, we define abstract simplicial complexes.
An abstract simplicial complex is a downwards-closed collection of nonempty finite sets containing
every Singleton. These are defined first defining `PreAbstractSimplicialComplex`,
which does not require the presence of singletons, and then defining `AbstractSimplicialComplex` as
an extension.

This is related to the geometrical notion of simplicial complexes, which are then defined under the
name `Geometry.SimplicialComplex` using affine combinations in another file.

## Main declarations

* `PreAbstractSimplicialComplex ι`: An abstract simplicial complex with vertices of type `ι`.
* `AbstractSimplicialComplex ι`: An abstract simplicial complex with vertices of type `ι` which
  contains all singletons.

## Notation

`s ∈ K` means that `s` is a face of `K`.

`K ≤ L` means that the faces of `K` are faces of `L`.

-/

@[expose] public section


open Finset Set

variable (ι : Type*)

/-- An abstract simplicial complex is a collection of nonempty finite sets of points ("faces")
which is downwards closed, i.e., any nonempty subset of a face is also a face.
-/
@[ext]
structure PreAbstractSimplicialComplex where
  /-- the faces of this simplicial complex: currently, given by their spanning vertices -/
  faces : Set (Finset ι)
  /-- the empty set is not a face: hence, all faces are non-empty -/
  empty_notMem : ∅ ∉ faces
  /-- faces are downward closed: a non-empty subset of its spanning vertices spans another face -/
  down_closed : ∀ {s t}, s ∈ faces → t ⊆ s → t.Nonempty → t ∈ faces

namespace PreAbstractSimplicialComplex

/-- The complex consisting of only the faces present in both of its arguments. -/
instance : Min (PreAbstractSimplicialComplex ι) :=
  ⟨fun K L =>
    { faces := K.faces ∩ L.faces
      empty_notMem := fun h => K.empty_notMem (Set.inter_subset_left h)
      down_closed := fun hs hst ht => ⟨K.down_closed hs.1 hst ht, L.down_closed hs.2 hst ht⟩ }⟩

/-- The complex consisting of all faces present in either of its arguments. -/
instance : Max (PreAbstractSimplicialComplex ι) :=
  ⟨fun K L =>
    { faces := K.faces ∪ L.faces
      empty_notMem := by
        simp only [Set.mem_union, not_or]
        exact ⟨K.empty_notMem, L.empty_notMem⟩
      down_closed := by
        sorry }⟩

instance : LE (PreAbstractSimplicialComplex ι) :=
  ⟨fun K L => K.faces ⊆ L.faces⟩

instance : LT (PreAbstractSimplicialComplex ι) :=
  ⟨fun K L => K.faces ⊂ L.faces⟩

instance : CompleteLattice (PreAbstractSimplicialComplex ι) where
  le := (· ≤ ·)
  lt := (· < ·)
  le_refl := fun K => Set.Subset.refl K.faces
  le_trans := fun _ _ _ h1 h2 => Set.Subset.trans h1 h2
  le_antisymm := fun K L h1 h2 => PreAbstractSimplicialComplex.ext (Set.Subset.antisymm h1 h2)
  sup := max
  le_sup_left := fun K L => Set.subset_union_left
  le_sup_right := fun K L => Set.subset_union_right
  sup_le := fun K L M h1 h2 => Set.union_subset h1 h2
  inf := min
  inf_le_left := fun K L => Set.inter_subset_left
  inf_le_right := fun K L => Set.inter_subset_right
  le_inf := fun K L M h1 h2 => Set.subset_inter h1 h2
  sSup := fun s =>
    { faces := ⋃ K ∈ s, K.faces
      empty_notMem := by
        simp only [Set.mem_iUnion, not_exists]
        exact fun K hK => K.empty_notMem
      down_closed := by
        sorry }
  le_sSup := fun s K hK => sorry
  sSup_le := fun s K hK => sorry
  sInf := fun s =>
    { faces := ⋂ K ∈ s, K.faces
      empty_notMem := by
        simp only [Set.mem_iInter, not_forall]
        sorry
      down_closed := by
        sorry }
  sInf_le := fun s K hK => sorry
  le_sInf := fun s K hK => sorry
  top :=
    { faces := { s | False }
      empty_notMem := by simp
      down_closed := by
        sorry }
  le_top := fun K s hs => sorry
  bot :=
    { faces := { s | s.Nonempty }
      empty_notMem := by simp
      down_closed := by
        sorry }
  bot_le := fun K s hs => sorry


end PreAbstractSimplicialComplex

@[ext]
structure AbstractSimplicialComplex extends PreAbstractSimplicialComplex ι where
  /-- every singleton is a face -/
  singleton_mem : ∀ v : ι, {v} ∈ faces

-- TODO typeclasses for lattice
-- TODO API to go from PreAbstractSimplicialComplex to AbstractSimplicialComplex and back

end
