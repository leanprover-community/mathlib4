/-
Copyright (c) 2025 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.Independent
public import Mathlib.Order.UpperLower.Relative

/-!
# Abstract Simplicial complexes

In this file, we define abstract simplicial complexes.
An abstract simplicial complex is a downwards-closed collection of nonempty finite sets containing
every singleton. These are defined first defining `PreAbstractSimplicialComplex`,
which does not require the presence of singletons, and then defining `AbstractSimplicialComplex` as
an extension.

This is related to the geometrical notion of simplicial complexes, which are then defined under the
name `Geometry.SimplicialComplex` using affine combinations in another file.

## Main declarations

* `PreAbstractSimplicialComplex ι`: An abstract simplicial complex with vertices of type `ι`.
* `AbstractSimplicialComplex ι`: An abstract simplicial complex with vertices of type `ι` which
  contains all singletons.

## Notation

* `s ∈ K` means that `s` is a face of `K`. This notation arises from a `SetLike` instance.
* `K ≤ L` means that the faces of `K` are faces of `L`.

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
  /-- Faces are nonempty and downward closed: a non-empty subset of its spanning vertices spans
  another face. -/
  isRelLowerSet_faces : IsRelLowerSet faces Finset.Nonempty

namespace PreAbstractSimplicialComplex

instance : SetLike (PreAbstractSimplicialComplex ι) (Finset ι) where
  coe K := K.faces
  coe_injective' K _ _ := by
    cases K
    congr

/-- The complex consisting of only the faces present in both of its arguments. -/
instance : Min (PreAbstractSimplicialComplex ι) where
  min K L :=
    { faces := K.faces ∩ L.faces
      isRelLowerSet_faces := IsRelLowerSet.inter K.isRelLowerSet_faces L.isRelLowerSet_faces }

/-- The complex consisting of all faces present in either of its arguments. -/
instance : Max (PreAbstractSimplicialComplex ι) where
  max K L :=
    { faces := K.faces ∪ L.faces
      isRelLowerSet_faces := IsRelLowerSet.union K.isRelLowerSet_faces L.isRelLowerSet_faces }

instance : LE (PreAbstractSimplicialComplex ι) where
  le K L := K.faces ⊆ L.faces

instance : LT (PreAbstractSimplicialComplex ι) where
  lt K L := K.faces ⊂ L.faces

instance : PartialOrder (PreAbstractSimplicialComplex ι) :=
  PartialOrder.lift (fun K => K.faces) (fun _ _ => PreAbstractSimplicialComplex.ext)

instance : SupSet (PreAbstractSimplicialComplex ι) where
  sSup s :=
    { faces := ⋃ K ∈ s, K.faces
      isRelLowerSet_faces := IsRelLowerSet.iUnion₂ fun K _ => K.isRelLowerSet_faces }

instance : InfSet (PreAbstractSimplicialComplex ι) where
  sInf s :=
    { faces := (⋂ K ∈ s, K.faces) ∩ { t | t.Nonempty }
      isRelLowerSet_faces := fun {_} ⟨hx, hn⟩ => by
        grind [IsRelLowerSet.mem_of_le, isRelLowerSet_faces, mem_iInter] }

instance : Top (PreAbstractSimplicialComplex ι) where
  top :=
    { faces := { s | s.Nonempty }
      isRelLowerSet_faces := fun {_} hs => ⟨hs, fun _ _ ht => ht⟩ }

instance : Bot (PreAbstractSimplicialComplex ι) where
  bot :=
    { faces := { _s | False }
      isRelLowerSet_faces := isRelLowerSet_empty }

instance : CompleteSemilatticeSup (PreAbstractSimplicialComplex ι) where
  le_sSup _ _ hK := Set.subset_biUnion_of_mem hK
  sSup_le _ _ hK := Set.iUnion₂_subset hK

instance : CompleteSemilatticeInf (PreAbstractSimplicialComplex ι) where
  sInf_le _ _ hK := Set.inter_subset_left.trans (Set.biInter_subset_of_mem hK)
  le_sInf _ K hK _ ht := ⟨Set.mem_iInter₂.mpr fun L hL => hK L hL ht, (K.isRelLowerSet_faces ht).1⟩

instance : CompleteLattice (PreAbstractSimplicialComplex ι) where
  inf := min
  inf_le_left _ _ := Set.inter_subset_left
  inf_le_right _ _ := Set.inter_subset_right
  le_inf _ _ _ := Set.subset_inter
  sup := max
  le_sup_left _ _ := Set.subset_union_left
  le_sup_right _ _ := Set.subset_union_right
  sup_le _ _ _ hK hL := Set.union_subset hK hL
  le_top K _ ht := (K.isRelLowerSet_faces ht).1
  bot_le _ _ ht := ht.elim

/--
Map each vertex in each face of a PreAbstractSimplicialComplex through a function,
producing a new PreAbstractSimplicialComplex.
-/
def map {α β : Type*} [DecidableEq β] (K : PreAbstractSimplicialComplex α) (f : α → β) :
    PreAbstractSimplicialComplex β where
  faces := K.faces.image (fun s => s.image f)
  isRelLowerSet_faces := fun {x} h => by
    simp only [Set.mem_image] at h ⊢
    obtain ⟨s', hs', rfl⟩ := h
    constructor
    · exact Finset.image_nonempty.mpr (K.isRelLowerSet_faces hs').1
    · intro t hts ht
      obtain ⟨t', ht', rfl⟩ := Finset.subset_image_iff.mp hts
      exact ⟨t', (K.isRelLowerSet_faces hs').2 ht' (Finset.image_nonempty.mp ht), rfl⟩

end PreAbstractSimplicialComplex


/--
An `AbstractSimplicialComplex` is a `PreAbstractSimplicialComplex` which contains all singletons.
-/
@[ext]
structure AbstractSimplicialComplex extends PreAbstractSimplicialComplex ι where
  /-- every singleton is a face -/
  singleton_mem : ∀ v : ι, {v} ∈ faces

/-- Convert a `PreAbstractSimplicialComplex` satisfying `IsAbstract` to an
`AbstractSimplicialComplex`. -/
def PreAbstractSimplicialComplex.toAbstractSimplicialComplex
    (K : PreAbstractSimplicialComplex ι) (h : ∀ v : ι, {v} ∈ K.faces) :
    AbstractSimplicialComplex ι :=
  { K with singleton_mem := h }

/-- The closure of a `PreAbstractSimplicialComplex` to an `AbstractSimplicialComplex` by adding
all singletons. -/
def PreAbstractSimplicialComplex.addSingletons
    (K : PreAbstractSimplicialComplex ι) :
    AbstractSimplicialComplex ι :=
  { faces := K.faces ∪ { s | ∃ v, s = {v} }
    isRelLowerSet_faces := IsRelLowerSet.union K.isRelLowerSet_faces (fun {x} ⟨v, hv⟩ => by
      constructor
      · rw [hv]; exact Finset.singleton_nonempty _
      · intro t hts ht
        cases Finset.subset_singleton_iff.mp (hv ▸ hts) with
        | inl h => exact (ht.ne_empty h).elim
        | inr h => exact ⟨v, h⟩)
    singleton_mem v := Or.inr ⟨v, rfl⟩ }

namespace AbstractSimplicialComplex

variable {ι}

instance : SetLike (AbstractSimplicialComplex ι) (Finset ι) where
  coe K := K.faces
  coe_injective' _ _ _ := by
    ext
    grind

/-- The complex consisting of only the faces present in both of its arguments. -/
instance : Min (AbstractSimplicialComplex ι) where
  min K L :=
    { K.toPreAbstractSimplicialComplex ⊓ L.toPreAbstractSimplicialComplex with
      singleton_mem v := ⟨K.singleton_mem v, L.singleton_mem v⟩ }

/-- The complex consisting of all faces present in either of its arguments. -/
instance : Max (AbstractSimplicialComplex ι) where
  max K L :=
    { K.toPreAbstractSimplicialComplex ⊔ L.toPreAbstractSimplicialComplex with
      singleton_mem v := Or.inl (K.singleton_mem v) }

instance : LE (AbstractSimplicialComplex ι) where
  le K L := K.faces ⊆ L.faces

instance : LT (AbstractSimplicialComplex ι) where
  lt K L := K.faces ⊂ L.faces

instance : PartialOrder (AbstractSimplicialComplex ι) :=
  PartialOrder.lift (fun K => K.faces) (fun _ _ => AbstractSimplicialComplex.ext)

theorem toPreAbstractSimplicialComplex_injective :
    Function.Injective (toPreAbstractSimplicialComplex (ι := ι)) :=
  fun _ _ h => AbstractSimplicialComplex.ext (congrArg PreAbstractSimplicialComplex.faces h)

@[simp]
theorem toPreAbstractSimplicialComplex_le_iff {K L : AbstractSimplicialComplex ι} :
    K.toPreAbstractSimplicialComplex ≤ L.toPreAbstractSimplicialComplex ↔ K ≤ L :=
  Iff.rfl

@[simp]
theorem toPreAbstractSimplicialComplex_lt_iff {K L : AbstractSimplicialComplex ι} :
    K.toPreAbstractSimplicialComplex < L.toPreAbstractSimplicialComplex ↔ K < L :=
  Iff.rfl

instance : SupSet (AbstractSimplicialComplex ι) where
  sSup s :=
    { faces := (⋃ K ∈ s, K.faces) ∪ { t | ∃ v, t = {v} }
      isRelLowerSet_faces := IsRelLowerSet.union
        (IsRelLowerSet.iUnion₂ fun K _ => K.isRelLowerSet_faces)
        (fun {x} ⟨v, hv⟩ => by
          constructor
          · rw [hv]; exact Finset.singleton_nonempty _
          · intro t hts ht
            cases Finset.subset_singleton_iff.mp (hv ▸ hts) with
            | inl h => exact (ht.ne_empty h).elim
            | inr h => exact ⟨v, h⟩)
      singleton_mem v := Or.inr ⟨v, rfl⟩ }

instance : InfSet (AbstractSimplicialComplex ι) where
  sInf s :=
    { faces := (⋂ K ∈ s, K.faces) ∩ { t | t.Nonempty }
      isRelLowerSet_faces := fun {_} ⟨hx, hn⟩ => by
        grind [IsRelLowerSet.mem_of_le, PreAbstractSimplicialComplex.isRelLowerSet_faces,
          mem_iInter]
      singleton_mem v := by
        grind [Set.mem_iInter, Finset.singleton_nonempty, singleton_mem]  }

instance : Top (AbstractSimplicialComplex ι) where
  top :=
    { (⊤ : PreAbstractSimplicialComplex ι) with
      singleton_mem _ := Finset.singleton_nonempty _ }

lemma top_toPreAbstractSimplicialComplex :
    (⊤ : AbstractSimplicialComplex ι).toPreAbstractSimplicialComplex = ⊤ :=
  rfl

instance : Bot (AbstractSimplicialComplex ι) where
  bot :=
    { faces := { s | ∃ v, s = {v} }
      isRelLowerSet_faces := fun {x} ⟨v, hv⟩ => by
        constructor
        · rw [hv]; exact Finset.singleton_nonempty _
        · intro t hts ht
          cases Finset.subset_singleton_iff.mp (hv ▸ hts) with
          | inl h => exact (ht.ne_empty h).elim
          | inr h => exact ⟨v, h⟩
      singleton_mem v := ⟨v, rfl⟩ }

instance : CompleteSemilatticeSup (AbstractSimplicialComplex ι) where
  le_sSup _ K hK _ ht := Or.inl (Set.mem_biUnion hK ht)
  sSup_le _ L hL _ ht := by
    cases ht with
    | inl ht =>
      simp only [Set.mem_iUnion] at ht
      obtain ⟨K, hK, htK⟩ := ht
      exact hL K hK htK
    | inr ht =>
      obtain ⟨v, hv⟩ := ht
      exact hv ▸ L.singleton_mem v

instance : CompleteSemilatticeInf (AbstractSimplicialComplex ι) where
  sInf_le _ _ hK := Set.inter_subset_left.trans (Set.biInter_subset_of_mem hK)
  le_sInf _ K hK _ ht := ⟨Set.mem_iInter₂.mpr fun L hL => hK L hL ht, (K.isRelLowerSet_faces ht).1⟩

instance : CompleteLattice (AbstractSimplicialComplex ι) where
  inf := min
  inf_le_left _ _ := Set.inter_subset_left
  inf_le_right _ _ := Set.inter_subset_right
  le_inf _ _ _ := Set.subset_inter
  sup := max
  le_sup_left _ _ := Set.subset_union_left
  le_sup_right _ _ := Set.subset_union_right
  sup_le _ _ _ := Set.union_subset
  le_top K _ ht := (K.isRelLowerSet_faces ht).1
  bot_le K _ ht := by
    obtain ⟨v, hv⟩ := ht
    exact hv ▸ K.singleton_mem v

end AbstractSimplicialComplex

end
