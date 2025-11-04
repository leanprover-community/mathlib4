/-
Copyright (c) 2025 Weijie Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weijie Jiang
-/
import Mathlib.Analysis.Convex.Segment
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Real.Basic

/-!
# Planar and Linear Graphs

This file defines planar embeddings and linear graphs in the context of simple graphs.

* A **planar embedding** assigns vertices to distinct points in the plane such that edges
  (as straight line segments) intersect only at shared endpoints.

* A **linear graph** is a special case of planar embedding where all vertices lie on a straight line
  and edges connect only consecutively ordered vertices, representing path graphs.

* A graph is **planar** if it admits a planar embedding.

* A graph is **linear** if it admits a linear embedding.

## Main definitions

* `PlanarEmbedding` : Structure capturing a crossing-free drawing of a graph in the plane.

* `LinearGraph` : Structure for graphs embeddable as paths on a line.

* `SimpleGraph.IsPlanar` : Proposition that a graph has a planar embedding.

* `SimpleGraph.IsLinearGraph` : Proposition that a graph has a linear embedding.

## Implementation notes

The planar embedding definition
  uses open segments to ensure edges don't intersect except at endpoints.
The linear graph definition
  requires vertices to be collinear and edges to connect consecutive vertices.

## Tags
planar graphs, linear graphs, graph embeddings, graph drawing
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
A **linear graph** is a graph whose vertices can be placed on a straight line in the plane,
preserving their linear order, such that edges only connect consecutively ordered vertices.
This represents a path graph embedded on a line.
-/
structure LinearGraph (V : Type*) [LinearOrder V] (G : SimpleGraph V)
  extends PlanarEmbedding V G where
  order_embed : V → ℝ
  order_preserving : ∀ u v, order_embed u ≤ order_embed v ↔ u ≤ v
  on_line : ∀ v, embed v = (order_embed v, 0)
  edges_are_adjacent : ∀ u v, G.Adj u v ↔ u < v ∧ ∀ w, u < w → w < v → ¬G.Adj u w

/--
A graph is **planar** if there exists a planar embedding.
-/
def IsPlanar {V : Type*} (G : SimpleGraph V) : Prop :=
  Nonempty (PlanarEmbedding V G)

/--
A graph is a **linear graph** if it admits a linear embedding,
i.e., it can be drawn as a path on a straight line.
-/
def IsLinearGraph {V : Type*} [LinearOrder V] (G : SimpleGraph V) : Prop :=
  Nonempty (LinearGraph V G)

end SimpleGraph
