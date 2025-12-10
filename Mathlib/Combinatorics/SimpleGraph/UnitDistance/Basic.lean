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

This module defines unit-distance graph embeddings into arbitrary metric spaces.
-/

@[expose] public section

namespace SimpleGraph

/-- A unit-distance embedding of a graph into a metric space is a vertex embedding
such that adjacent vertices are at distance 1 from each other. -/
structure UDEmbedding {V : Type*} (E : Type*) [MetricSpace E] (G : SimpleGraph V) where
  /-- The embedding itself (position of vertices) -/
  p : V ↪ E
  /-- The distance between any two adjacent vertices is 1. -/
  unit_dist {u v} (ha : G.Adj u v) : dist (p u) (p v) = 1

end SimpleGraph
