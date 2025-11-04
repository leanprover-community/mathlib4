/-
Copyright (c) 2025 Weijie Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weijie Jiang
-/
import Mathlib.Analysis.Convex.Segment
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Real.Basic

/-!
# Planar Graphs

This file defines planar embeddings in the context of simple graphs.

* A **planar embedding** assigns vertices to distinct points in the plane such that edges
  (as straight line segments) intersect only at shared endpoints.

* A graph is **planar** if it admits a planar embedding.

## Main definitions

* `PlanarEmbedding` : Structure capturing a crossing-free drawing of a graph in the plane.

* `SimpleGraph.IsPlanar` : Proposition that a graph has a planar embedding.

## Tags
planar graphs, graph embeddings
-/

namespace SimpleGraph
variable {V : Type*} [LinearOrder V] {G : SimpleGraph V}

/--
A **planar embedding** of a simple graph `G` is an assignment of each vertex to a distinct point
in the Euclidean plane, such that:
- Each edge is represented by the straight line segment between its endpoints
- No two edges intersect except possibly at their shared endpoints

This structure ensures the graph can be drawn in the plane without edge crossings.
-/
structure PlanarEmbedding (V : Type*) (G : SimpleGraph V) where
  embed : V → ℝ × ℝ
  inj : Function.Injective embed
  edge_segments_disjoint :
    ∀ ⦃u v x y : V⦄,
      G.Adj u v → G.Adj x y →
      (u, v) ≠ (x, y) ∧ (u, v) ≠ (y, x) →
      Disjoint
        (openSegment ℝ (embed u) (embed v))
        (openSegment ℝ (embed x) (embed y))

/--
A graph is **planar** if there exists a planar embedding.
-/
def IsPlanar {V : Type*} (G : SimpleGraph V) : Prop :=
  Nonempty (PlanarEmbedding V G)

end SimpleGraph
