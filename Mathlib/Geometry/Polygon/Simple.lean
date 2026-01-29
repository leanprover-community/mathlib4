/-
Copyright (c) 2026 A. M. Berns. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: A. M. Berns
-/
import Mathlib.Geometry.Polygon.Basic
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.Order.Basic
import Mathlib.Algebra.Order.Ring.Basic


/-!
# Simple polygons (dimension-agnostic)

This file is meant to replicate the “simple polygon” API from `SimpleEuclideanPolygon.lean`,
but **without** hard-coding `EuclideanSpace ℝ (Fin 2)`.

The guiding outline is:

1. Define the boundary as a function `AddCircle (n : R) → P`.
2. Show `Set.range boundary = poly.boundary R`.
3. Define a “simple polygon” as one where this boundary map is injective.
4. Show this injectivity is equivalent to “edges are disjoint except at common vertices”.
5. Show continuity of the boundary map under whatever topological hypotheses are required.

Most results are currently **statements only** (`sorry`) to serve as a skeleton for porting.
-/

open Set Topology

namespace Polygon

variable {R V P : Type*} {n : ℕ}
variable [LinearOrder R] [Ring R] [FloorRing R] [IsStrictOrderedRing R] [Archimedean R]
variable [AddCommGroup V] [Module R V] [AddTorsor V P]
variable [NeZero n]

noncomputable def boundaryMap (poly : Polygon P n) : R → P := fun t =>
  if _ : t = (n : R) then
    poly 0
  else
    let k : ℕ := (Int.floor t).toNat % n
    let i : Fin n := ⟨k, Nat.mod_lt _ (NeZero.pos n)⟩
    let t' : R := t - (i : ℕ)
    poly.edgePath R i t'

/-- Endpoint agreement needed to lift `boundaryMap` to the circle. -/
lemma boundaryMap_zero_eq_n (poly : Polygon P n) :
    poly.boundaryMap (0 : R) = poly.boundaryMap (n : R) := by
  unfold boundaryMap
  simp only [zero_sub, dite_eq_ite, ↓reduceDIte, ite_eq_left_iff]
  by_cases h : (0 : R) = (n : R)
  · intro h'
    contradiction
  have hk : (Int.floor (0 : R)).toNat % n = 0 := by
    simp only [Int.floor_zero, Int.toNat_zero, Nat.zero_mod]
  simp only [hk]
  unfold edgePath
  simp


section Archimedean

noncomputable def boundaryCircle (poly : Polygon P n) : AddCircle (n : R) → P :=
  have hnR : (0 : R) < (n : R) := by
    exact_mod_cast (NeZero.pos n)
  haveI : Fact (0 < (n : R)) := ⟨hnR⟩
  AddCircle.liftIco (n : R) (0 : R) poly.boundaryMap

/-- `range boundaryCircle` is the union of all edges (i.e. `poly.boundary R`). -/
lemma range_boundaryCircle_eq_boundary (poly : Polygon P n) :
  Set.range (boundaryCircle (R := R) poly) = poly.boundary R := by
  -- TODO: use `AddCircle.liftIco_range`-style lemmas and the definition of `Polygon.boundary`.
  -- Goal: show points in the range come from some `t ∈ Ico 0 n`, hence from some edge `i`,
  -- and conversely each edge image appears.
  sorry



/-! ## 3. Simplicity as injectivity of the boundary map -/

/-- A polygon is *simple* if its boundary parameterization on the circle is injective. -/
def IsSimple (poly : Polygon P n) : Prop :=
  Function.Injective (boundaryCircle (R := R) poly)

/-! ## 4. “Edges disjoint except at common vertices” formulation -/

/-- Edges are disjoint except at (shared) adjacent vertices.

This is the formulation you used in `SimpleEuclideanPolygon` but stated for general `P` and `R`. -/
structure EdgesDisjointExceptVertices (poly : Polygon P n) : Prop :=
  (non_adjacent_edges_disjoint :
      ∀ i j : Fin n,
        (j ≠ i ∧ j ≠ i + 1 ∧ i ≠ j + 1) →
          Disjoint (poly.edgeSet R i) (poly.edgeSet R j))
  (adjacent_edges_inter :
      ∀ i : Fin n,
        (poly.edgeSet R i ∩ poly.edgeSet R (i + 1)) = ({poly (i + 1)} : Set P))
  (adj_vertices_distinct : ∀ i : Fin n, poly i ≠ poly (i + 1))

/-- Injectivity of `boundaryCircle` implies edge-disjointness (except at vertices). -/
theorem edgesDisjointExceptVertices_of_isSimple
    (poly : Polygon P n) (hs : IsSimple (R:= R) poly) :
    EdgesDisjointExceptVertices (R := R) poly := by
  classical
  -- TODO: port the “two parameters map to same point ⇒ same edge and same local parameter”
  -- argument, and extract edge-disjointness consequences.
  sorry

/-- Edge-disjointness (except at vertices) implies injectivity of `boundaryCircle`. -/
theorem isSimple_of_edgesDisjointExceptVertices
    (poly : Polygon P n) (h : EdgesDisjointExceptVertices (R := R) poly) :
    poly.IsSimple := by
  classical
  -- TODO: port the global injectivity proof using:
  -- * `edgePath` injective on the local parameter interval (requires `adj_vertices_distinct`)
  -- * non-adjacent edges disjoint
  -- * adjacent edges intersect only at the shared vertex
  sorry

/-- Main equivalence: “simple” ↔ “edges disjoint except at common vertices”. -/
theorem isSimple_iff_edgesDisjointExceptVertices (poly : Polygon P n) :
    poly.IsSimple ↔ EdgesDisjointExceptVertices (R := R) poly := by
  constructor
  · intro hs; exact edgesDisjointExceptVertices_of_isSimple (R := R) poly hs
  · intro h;  exact isSimple_of_edgesDisjointExceptVertices (R := R) poly h

section Continuity
variable [TopologicalSpace R] [TopologicalSpace P]

lemma boundaryMap_continuousOn_piece
    [TopologicalSpace R] [TopologicalSpace V] [TopologicalSpace P]
    (poly : Polygon P n) (k : Fin n) :
    ContinuousOn poly.boundaryMap (Icc (k : R) ((k : ℕ) + 1 : ℕ)) := by
  classical
  -- TODO: likely easier to restate the piece interval as `Icc (k : R) (k+1)` in `R`
  -- (with casts) and use continuity of `AffineMap.lineMap`.
  sorry

/-- Continuity on the whole base interval `Icc (0 : R) n` (skeleton). -/
lemma boundaryMap_continuousOn
    (poly : Polygon P n) :
    ContinuousOn poly.boundaryMap (Icc (0 : R) (n : R)) := by
  sorry

/-- Continuity of the boundary map on the circle. -/
lemma boundaryCircle_continuous (poly : Polygon P n) : Continuous poly.boundaryCircle := by
  -- TODO: `AddCircle.liftIco_continuous` with
  -- * `boundaryMap_zero_eq_n`
  -- * `boundaryMap_continuousOn`
  sorry

end Continuity

end Archimedean

end Polygon
