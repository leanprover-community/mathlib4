/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import Mathlib.Analysis.Convex.Hull
import Mathlib.LinearAlgebra.AffineSpace.Independent

#align_import analysis.convex.simplicial_complex.basic from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

/-!
# Simplicial complexes

In this file, we define simplicial complexes in `𝕜`-modules. A simplicial complex is a collection
of simplices closed by inclusion (of vertices) and intersection (of underlying sets).

We model them by a downward-closed set of affine independent finite sets whose convex hulls "glue
nicely", each finite set and its convex hull corresponding respectively to the vertices and the
underlying set of a simplex.

## Main declarations

* `SimplicialComplex 𝕜 E`: A simplicial complex in the `𝕜`-module `E`.
* `SimplicialComplex.vertices`: The zero dimensional faces of a simplicial complex.
* `SimplicialComplex.facets`: The maximal faces of a simplicial complex.

## Notation

`s ∈ K` means that `s` is a face of `K`.

`K ≤ L` means that the faces of `K` are faces of `L`.

## Implementation notes

"glue nicely" usually means that the intersection of two faces (as sets in the ambient space) is a
face. Given that we store the vertices, not the faces, this would be a bit awkward to spell.
Instead, `SimplicialComplex.inter_subset_convexHull` is an equivalent condition which works on the
vertices.

## TODO

Simplicial complexes can be generalized to affine spaces once `ConvexHull` has been ported.
-/


open Finset Set

variable (𝕜 E : Type*) {ι : Type*} [OrderedRing 𝕜] [AddCommGroup E] [Module 𝕜 E]

namespace Geometry

-- TODO: update to new binder order? not sure what binder order is correct for `down_closed`.
/-- A simplicial complex in a `𝕜`-module is a collection of simplices which glue nicely together.
Note that the textbook meaning of "glue nicely" is given in
`Geometry.SimplicialComplex.disjoint_or_exists_inter_eq_convexHull`. It is mostly useless, as
`Geometry.SimplicialComplex.convexHull_inter_convexHull` is enough for all purposes. -/
@[ext]
structure SimplicialComplex where
  /-- the faces of this simplicial complex: currently, given by their spanning vertices -/
  faces : Set (Finset E)
  /-- the empty set is not a face: hence, all faces are non-empty -/
  not_empty_mem : ∅ ∉ faces
  /-- the vertices in each face are affine independent: this is an implementation detail -/
  indep : ∀ {s}, s ∈ faces → AffineIndependent 𝕜 ((↑) : s → E)
  /-- faces are downward closed: a non-empty subset of its spanning vertices spans another face -/
  down_closed : ∀ {s t}, s ∈ faces → t ⊆ s → t ≠ ∅ → t ∈ faces
  inter_subset_convexHull : ∀ {s t}, s ∈ faces → t ∈ faces →
    convexHull 𝕜 ↑s ∩ convexHull 𝕜 ↑t ⊆ convexHull 𝕜 (s ∩ t : Set E)
#align geometry.simplicial_complex Geometry.SimplicialComplex

namespace SimplicialComplex

variable {𝕜 E}
variable {K : SimplicialComplex 𝕜 E} {s t : Finset E} {x : E}

/-- A `Finset` belongs to a `SimplicialComplex` if it's a face of it. -/
instance : Membership (Finset E) (SimplicialComplex 𝕜 E) :=
  ⟨fun s K => s ∈ K.faces⟩

/-- The underlying space of a simplicial complex is the union of its faces. -/
def space (K : SimplicialComplex 𝕜 E) : Set E :=
  ⋃ s ∈ K.faces, convexHull 𝕜 (s : Set E)
#align geometry.simplicial_complex.space Geometry.SimplicialComplex.space

-- Porting note: Expanded `∃ s ∈ K.faces` to get the type to match more closely with Lean 3
theorem mem_space_iff : x ∈ K.space ↔ ∃ s ∈ K.faces, x ∈ convexHull 𝕜 (s : Set E) := by
  simp [space]
#align geometry.simplicial_complex.mem_space_iff Geometry.SimplicialComplex.mem_space_iff

-- Porting note: Original proof was `:= subset_biUnion_of_mem hs`
theorem convexHull_subset_space (hs : s ∈ K.faces) : convexHull 𝕜 ↑s ⊆ K.space := by
  convert subset_biUnion_of_mem hs
  rfl
#align geometry.simplicial_complex.convex_hull_subset_space Geometry.SimplicialComplex.convexHull_subset_space

protected theorem subset_space (hs : s ∈ K.faces) : (s : Set E) ⊆ K.space :=
  (subset_convexHull 𝕜 _).trans <| convexHull_subset_space hs
#align geometry.simplicial_complex.subset_space Geometry.SimplicialComplex.subset_space

theorem convexHull_inter_convexHull (hs : s ∈ K.faces) (ht : t ∈ K.faces) :
    convexHull 𝕜 ↑s ∩ convexHull 𝕜 ↑t = convexHull 𝕜 (s ∩ t : Set E) :=
  (K.inter_subset_convexHull hs ht).antisymm <|
    subset_inter (convexHull_mono <| Set.inter_subset_left _ _) <|
      convexHull_mono <| Set.inter_subset_right _ _
#align geometry.simplicial_complex.convex_hull_inter_convex_hull Geometry.SimplicialComplex.convexHull_inter_convexHull

/-- The conclusion is the usual meaning of "glue nicely" in textbooks. It turns out to be quite
unusable, as it's about faces as sets in space rather than simplices. Further, additional structure
on `𝕜` means the only choice of `u` is `s ∩ t` (but it's hard to prove). -/
theorem disjoint_or_exists_inter_eq_convexHull (hs : s ∈ K.faces) (ht : t ∈ K.faces) :
    Disjoint (convexHull 𝕜 (s : Set E)) (convexHull 𝕜 ↑t) ∨
      ∃ u ∈ K.faces, convexHull 𝕜 (s : Set E) ∩ convexHull 𝕜 ↑t = convexHull 𝕜 ↑u := by
  classical
  by_contra! h
  refine h.2 (s ∩ t) (K.down_closed hs (inter_subset_left _ _) fun hst => h.1 <|
    disjoint_iff_inf_le.mpr <| (K.inter_subset_convexHull hs ht).trans ?_) ?_
  · rw [← coe_inter, hst, coe_empty, convexHull_empty]
    rfl
  · rw [coe_inter, convexHull_inter_convexHull hs ht]
#align geometry.simplicial_complex.disjoint_or_exists_inter_eq_convex_hull Geometry.SimplicialComplex.disjoint_or_exists_inter_eq_convexHull

/-- Construct a simplicial complex by removing the empty face for you. -/
@[simps]
def ofErase (faces : Set (Finset E)) (indep : ∀ s ∈ faces, AffineIndependent 𝕜 ((↑) : s → E))
    (down_closed : ∀ s ∈ faces, ∀ t ⊆ s, t ∈ faces)
    (inter_subset_convexHull : ∀ᵉ (s ∈ faces) (t ∈ faces),
      convexHull 𝕜 ↑s ∩ convexHull 𝕜 ↑t ⊆ convexHull 𝕜 (s ∩ t : Set E)) :
    SimplicialComplex 𝕜 E where
  faces := faces \ {∅}
  not_empty_mem h := h.2 (mem_singleton _)
  indep hs := indep _ hs.1
  down_closed hs hts ht := ⟨down_closed _ hs.1 _ hts, ht⟩
  inter_subset_convexHull hs ht := inter_subset_convexHull _ hs.1 _ ht.1
#align geometry.simplicial_complex.of_erase Geometry.SimplicialComplex.ofErase

/-- Construct a simplicial complex as a subset of a given simplicial complex. -/
@[simps]
def ofSubcomplex (K : SimplicialComplex 𝕜 E) (faces : Set (Finset E)) (subset : faces ⊆ K.faces)
    (down_closed : ∀ {s t}, s ∈ faces → t ⊆ s → t ∈ faces) : SimplicialComplex 𝕜 E :=
  { faces
    not_empty_mem := fun h => K.not_empty_mem (subset h)
    indep := fun hs => K.indep (subset hs)
    down_closed := fun hs hts _ => down_closed hs hts
    inter_subset_convexHull := fun hs ht => K.inter_subset_convexHull (subset hs) (subset ht) }
#align geometry.simplicial_complex.of_subcomplex Geometry.SimplicialComplex.ofSubcomplex

/-! ### Vertices -/


/-- The vertices of a simplicial complex are its zero dimensional faces. -/
def vertices (K : SimplicialComplex 𝕜 E) : Set E :=
  { x | {x} ∈ K.faces }
#align geometry.simplicial_complex.vertices Geometry.SimplicialComplex.vertices

theorem mem_vertices : x ∈ K.vertices ↔ {x} ∈ K.faces := Iff.rfl
#align geometry.simplicial_complex.mem_vertices Geometry.SimplicialComplex.mem_vertices

theorem vertices_eq : K.vertices = ⋃ k ∈ K.faces, (k : Set E) := by
  ext x
  refine ⟨fun h => mem_biUnion h <| mem_coe.2 <| mem_singleton_self x, fun h => ?_⟩
  obtain ⟨s, hs, hx⟩ := mem_iUnion₂.1 h
  exact K.down_closed hs (Finset.singleton_subset_iff.2 <| mem_coe.1 hx) (singleton_ne_empty _)
#align geometry.simplicial_complex.vertices_eq Geometry.SimplicialComplex.vertices_eq

theorem vertices_subset_space : K.vertices ⊆ K.space :=
  vertices_eq.subset.trans <| iUnion₂_mono fun x _ => subset_convexHull 𝕜 (x : Set E)
#align geometry.simplicial_complex.vertices_subset_space Geometry.SimplicialComplex.vertices_subset_space

theorem vertex_mem_convexHull_iff (hx : x ∈ K.vertices) (hs : s ∈ K.faces) :
    x ∈ convexHull 𝕜 (s : Set E) ↔ x ∈ s := by
  refine ⟨fun h => ?_, fun h => subset_convexHull 𝕜 _ h⟩
  classical
  have h := K.inter_subset_convexHull hx hs ⟨by simp, h⟩
  by_contra H
  rwa [← coe_inter, Finset.disjoint_iff_inter_eq_empty.1 (Finset.disjoint_singleton_right.2 H).symm,
    coe_empty, convexHull_empty] at h
#align geometry.simplicial_complex.vertex_mem_convex_hull_iff Geometry.SimplicialComplex.vertex_mem_convexHull_iff

/-- A face is a subset of another one iff its vertices are. -/
theorem face_subset_face_iff (hs : s ∈ K.faces) (ht : t ∈ K.faces) :
    convexHull 𝕜 (s : Set E) ⊆ convexHull 𝕜 ↑t ↔ s ⊆ t :=
  ⟨fun h _ hxs =>
    (vertex_mem_convexHull_iff
          (K.down_closed hs (Finset.singleton_subset_iff.2 hxs) <| singleton_ne_empty _) ht).1
      (h (subset_convexHull 𝕜 (↑s) hxs)),
    convexHull_mono⟩
#align geometry.simplicial_complex.face_subset_face_iff Geometry.SimplicialComplex.face_subset_face_iff

/-! ### Facets -/


/-- A facet of a simplicial complex is a maximal face. -/
def facets (K : SimplicialComplex 𝕜 E) : Set (Finset E) :=
  { s ∈ K.faces | ∀ ⦃t⦄, t ∈ K.faces → s ⊆ t → s = t }
#align geometry.simplicial_complex.facets Geometry.SimplicialComplex.facets

theorem mem_facets : s ∈ K.facets ↔ s ∈ K.faces ∧ ∀ t ∈ K.faces, s ⊆ t → s = t :=
  mem_sep_iff
#align geometry.simplicial_complex.mem_facets Geometry.SimplicialComplex.mem_facets

theorem facets_subset : K.facets ⊆ K.faces := fun _ hs => hs.1
#align geometry.simplicial_complex.facets_subset Geometry.SimplicialComplex.facets_subset

theorem not_facet_iff_subface (hs : s ∈ K.faces) : s ∉ K.facets ↔ ∃ t, t ∈ K.faces ∧ s ⊂ t := by
  refine ⟨fun hs' : ¬(_ ∧ _) => ?_, ?_⟩
  · push_neg at hs'
    obtain ⟨t, ht⟩ := hs' hs
    exact ⟨t, ht.1, ⟨ht.2.1, fun hts => ht.2.2 (Subset.antisymm ht.2.1 hts)⟩⟩
  · rintro ⟨t, ht⟩ ⟨hs, hs'⟩
    have := hs' ht.1 ht.2.1
    rw [this] at ht
    exact ht.2.2 (Subset.refl t)
#align geometry.simplicial_complex.not_facet_iff_subface Geometry.SimplicialComplex.not_facet_iff_subface

/-!
### The semilattice of simplicial complexes

`K ≤ L` means that `K.faces ⊆ L.faces`.
-/


-- `HasSSubset.SSubset.ne` would be handy here
variable (𝕜 E)

/-- The complex consisting of only the faces present in both of its arguments. -/
instance : Inf (SimplicialComplex 𝕜 E) :=
  ⟨fun K L =>
    { faces := K.faces ∩ L.faces
      not_empty_mem := fun h => K.not_empty_mem (Set.inter_subset_left _ _ h)
      indep := fun hs => K.indep hs.1
      down_closed := fun hs hst ht => ⟨K.down_closed hs.1 hst ht, L.down_closed hs.2 hst ht⟩
      inter_subset_convexHull := fun hs ht => K.inter_subset_convexHull hs.1 ht.1 }⟩

instance : SemilatticeInf (SimplicialComplex 𝕜 E) :=
  { PartialOrder.lift faces SimplicialComplex.ext with
    inf := (· ⊓ ·)
    inf_le_left := fun _ _ _ hs => hs.1
    inf_le_right := fun _ _ _ hs => hs.2
    le_inf := fun _ _ _ hKL hKM _ hs => ⟨hKL hs, hKM hs⟩ }

instance hasBot : Bot (SimplicialComplex 𝕜 E) :=
  ⟨{  faces := ∅
      not_empty_mem := Set.not_mem_empty ∅
      indep := fun hs => (Set.not_mem_empty _ hs).elim
      down_closed := fun hs => (Set.not_mem_empty _ hs).elim
      inter_subset_convexHull := fun hs => (Set.not_mem_empty _ hs).elim }⟩

instance : OrderBot (SimplicialComplex 𝕜 E) :=
  { SimplicialComplex.hasBot 𝕜 E with bot_le := fun _ => Set.empty_subset _ }

instance : Inhabited (SimplicialComplex 𝕜 E) :=
  ⟨⊥⟩

variable {𝕜 E}

theorem faces_bot : (⊥ : SimplicialComplex 𝕜 E).faces = ∅ := rfl
#align geometry.simplicial_complex.faces_bot Geometry.SimplicialComplex.faces_bot

theorem space_bot : (⊥ : SimplicialComplex 𝕜 E).space = ∅ :=
  Set.biUnion_empty _
#align geometry.simplicial_complex.space_bot Geometry.SimplicialComplex.space_bot

theorem facets_bot : (⊥ : SimplicialComplex 𝕜 E).facets = ∅ :=
  eq_empty_of_subset_empty facets_subset
#align geometry.simplicial_complex.facets_bot Geometry.SimplicialComplex.facets_bot

end SimplicialComplex

end Geometry
