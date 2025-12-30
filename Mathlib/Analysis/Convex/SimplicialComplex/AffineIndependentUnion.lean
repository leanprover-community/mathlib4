/-
Copyright (c) 2025 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module

public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Convex.SimplicialComplex.Basic
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# Simplicial complexes from affinely independent points

This file provides constructions for simplicial complexes where the vertices
are affinely independent.

## Main declarations

* `Geometry.SimplicialComplex.ofAffineIndependent`: Construct a simplicial complex from a
  downward-closed set of faces whose union of vertices is affinely independent.
* `Geometry.SimplicialComplex.onFinsupp`: Construct a simplicial complex on `ι →₀ 𝕜` from a
  downward-closed set of finite subsets of `ι`, using the standard basis vectors.
* `Geometry.SimplicialComplex.ofSimpleGraph`: Construct a simplicial complex from a simple graph,
  where vertices of the graph are 0-simplices and edges are 1-simplices.
-/

@[expose] public section

open Finset Set

namespace Geometry

namespace AbstractSimplicialComplex

/--
Construct an abstract simplicial complex from a simple graph, where vertices of the graph
are 0-simplices and edges are 1-simplices.
-/
def ofSimpleGraph {ι : Type*} [DecidableEq ι] (G : SimpleGraph ι) :
    AbstractSimplicialComplex ι where
  faces := ((fun v => ({v} : Finset ι)) '' (Set.univ (α := ι))) ∪ Sym2.toFinset '' G.edgeSet
  empty_notMem := by
    simp only [Set.mem_union, Set.mem_image, Set.mem_univ, true_and, Finset.singleton_ne_empty,
      exists_false, false_or, not_exists, not_and]
    exact fun _ _ h => Finset.ne_empty_of_mem (Sym2.mem_toFinset.mpr (Sym2.out_fst_mem _)) h
  down_closed := by
    simp only [Set.mem_union, Set.mem_image, Set.mem_univ, true_and]
    intro s t hs hts ht
    rcases hs with ⟨v, rfl⟩ | ⟨e, he, rfl⟩
    · simp only [Finset.subset_singleton_iff] at hts
      rcases hts with rfl | rfl
      · exact ht.ne_empty rfl |>.elim
      · exact Or.inl ⟨v, rfl⟩
    · by_cases hc : t.card ≤ 1
      · left
        obtain ⟨x, hx⟩ := ht
        exact ⟨x, (Finset.eq_singleton_iff_unique_mem.mpr
          ⟨hx, fun y hy => Finset.card_le_one.mp hc y hy x hx⟩).symm⟩
      · right
        push_neg at hc
        have hle : e.toFinset.card ≤ t.card := by
          have := Sym2.card_toFinset e
          split_ifs at this <;> omega
        exact ⟨e, he, (Finset.eq_of_subset_of_card_le hts hle).symm⟩

end AbstractSimplicialComplex

namespace SimplicialComplex

/--
Construct a simplicial complex from a downward-closed set of faces
with defining points affinely independent.
-/
def ofAffineIndependent {𝕜 E}
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [DecidableEq E] [AddCommGroup E] [Module 𝕜 E]
    (faces : Set (Finset E)) (empty_notMem : ∅ ∉ faces)
    (down_closed : ∀ {s t}, s ∈ faces → t ⊆ s → t.Nonempty → t ∈ faces)
    (indep : AffineIndependent 𝕜 (Subtype.val : (⋃ s ∈ faces, (s : Set E)) → E)) :
    SimplicialComplex 𝕜 E where
  faces := faces
  empty_notMem := empty_notMem
  indep {s} hs := indep.mono (Set.subset_biUnion_of_mem hs)
  down_closed := down_closed
  inter_subset_convexHull {s t} hs ht := by
    apply subset_of_eq
    rw [AffineIndependent.convexHull_inter (R := 𝕜) (s := s ∪ t)]
    · apply indep.mono
      simp only [Finset.coe_union]
      exact Set.union_subset (Set.subset_biUnion_of_mem hs) (Set.subset_biUnion_of_mem ht)
    · exact Finset.subset_union_left
    · exact Finset.subset_union_right

/--
Construct a simplicial complex from an abstract simplicial complex on a set of points
over the `𝕜`-module of finitely supported functions on those points.
-/
noncomputable def onFinsupp {𝕜 ι : Type*} [DecidableEq ι]
    [DecidableEq 𝕜] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    (abstract : AbstractSimplicialComplex ι) :
    SimplicialComplex 𝕜 (ι →₀ 𝕜) :=
  ofAffineIndependent (𝕜 := 𝕜) (E := ι →₀ 𝕜)
    (abstract.faces.image (fun x => x.image (fun i => Finsupp.single i (1 : 𝕜))))
    (by
      simp only [Set.mem_image, Finset.image_eq_empty]
      rintro ⟨s, hs, rfl⟩
      exact abstract.empty_notMem hs)
    (by
      simp only [Set.mem_image]
      rintro _ t ⟨s', hs', rfl⟩ hts ht
      rw [Finset.subset_image_iff] at hts
      obtain ⟨t', ht', rfl⟩ := hts
      exact ⟨t', abstract.down_closed hs' ht' (Finset.image_nonempty.mp ht), rfl⟩)
    (by
      refine (Finsupp.linearIndependent_single_one 𝕜 ι).affineIndependent.range.mono fun x hx => ?_
      simp only [Set.mem_iUnion, Set.mem_image, Finset.mem_coe] at hx
      obtain ⟨_, ⟨_, _, rfl⟩, hx⟩ := hx
      exact Finset.mem_image.mp hx |>.choose_spec.2 ▸ Set.mem_range_self _)

/--
The simplicial complex associated to a simple graph, where vertices of the graph
are 0-simplices and edges are 1-simplices. The complex is constructed over the
`𝕜`-module of finitely supported functions on the vertex type.
-/
noncomputable def ofSimpleGraph {𝕜 V : Type*} [DecidableEq V] [DecidableEq 𝕜]
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    (G : SimpleGraph V) :
    SimplicialComplex 𝕜 (V →₀ 𝕜) :=
  onFinsupp (AbstractSimplicialComplex.ofSimpleGraph G)

end SimplicialComplex

end Geometry
