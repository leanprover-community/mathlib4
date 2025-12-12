/-
Copyright (c) 2025 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Topology.MetricSpace.Defs

/-!
# Unit-distance graph embeddings

An embedding of a graph into some metric space is _unit-distance_ if the distance between any two
adjacent vertices is 1. The space in question is usually the Euclidean plane, but can also be
higher-dimensional Euclidean space or the sphere (cf. [Frankl_2020]). We do not require nonadjacent
vertices to not be distance 1 apart as [hong2014] does.

## Main definitions

* `UnitDistEmbedding E G` is a unit-distance embedding of `G` into `E`.
-/

@[expose] public section

namespace SimpleGraph

/-- A unit-distance embedding of a graph into a metric space is a vertex embedding
such that adjacent vertices are at distance 1 from each other. -/
structure UnitDistEmbedding {V : Type*} (E : Type*) [MetricSpace E] (G : SimpleGraph V) where
  /-- The embedding itself (position of vertices) -/
  p : V ↪ E
  /-- The distance between any two adjacent vertices is 1. -/
  unit_dist {u v} (ha : G.Adj u v) : dist (p u) (p v) = 1

end SimpleGraph
