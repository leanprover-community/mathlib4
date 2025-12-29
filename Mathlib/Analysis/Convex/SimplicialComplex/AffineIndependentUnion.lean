/-
Copyright (c) 2025 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module

public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Convex.SimplicialComplex.Basic
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-!
# Simplicial complexes from affinely independent points

This file provides constructions for simplicial complexes where the vertices
are affinely independent.

## Main declarations

* `Geometry.SimplicialComplex.ofAffineIndependent`: Construct a simplicial complex from a
  downward-closed set of faces whose union of vertices is affinely independent.
* `Geometry.SimplicialComplex.onFinsupp`: Construct a simplicial complex on `ι →₀ 𝕜` from a
  downward-closed set of finite subsets of `ι`, using the standard basis vectors.
-/

@[expose] public section

open Finset Set

-- TODO find home
open Classical in
theorem AffineIndependent.Finsupp {𝕜 ι : Type*} [inst : Ring 𝕜] :
    AffineIndependent 𝕜 (V := ι →₀ 𝕜) (P := ι →₀ 𝕜) fun i ↦ Finsupp.single i 1 := by
  intro s w hw0 hwv i hi
  rw [Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero _ _ _ hw0 0,
    Finset.weightedVSubOfPoint_apply] at hwv
  simp only [vsub_eq_sub, sub_zero] at hwv
  exact (linearIndependent_iff'.mp (Finsupp.linearIndependent_single_one 𝕜 ι)) s w hwv i hi


namespace Geometry

namespace SimplicialComplex

open Classical in
/--
Construct a simplicial complex from a downward-closed set of faces
with defining points affinely independent.
-/
def ofAffineIndependent {𝕜 E}
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup E] [Module 𝕜 E]
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

open Classical in
/--
Construct a simplicial complex from a downward-closed set of points
over the `𝕜`-module of finitely supported functions on those points.
-/
def onFinsupp {𝕜 ι : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    (faces : Set (Finset ι))
    (empty_notMem : ∅ ∉ faces)
    (down_closed : ∀ {s t}, s ∈ faces → t ⊆ s → t.Nonempty → t ∈ faces) :
    SimplicialComplex 𝕜 (ι →₀ 𝕜) :=
  ofAffineIndependent (𝕜 := 𝕜) (E := ι →₀ 𝕜)
    (faces.image (fun x => x.image (fun i => Finsupp.single i (1 : 𝕜))))
    (by
      simp only [Set.mem_image, Finset.image_eq_empty]
      rintro ⟨s, hs, rfl⟩
      exact empty_notMem hs)
    (by
      simp only [Set.mem_image]
      rintro _ t ⟨s', hs', rfl⟩ hts ht
      rw [Finset.subset_image_iff] at hts
      obtain ⟨t', ht', rfl⟩ := hts
      exact ⟨t', down_closed hs' ht' (Finset.image_nonempty.mp ht), rfl⟩)
    (by
      refine AffineIndependent.Finsupp.range.mono fun x hx => ?_
      simp only [Set.mem_iUnion, Set.mem_image, Finset.mem_coe] at hx
      obtain ⟨_, ⟨_, _, rfl⟩, hx⟩ := hx
      exact Finset.mem_image.mp hx |>.choose_spec.2 ▸ Set.mem_range_self _)

end SimplicialComplex

end Geometry
