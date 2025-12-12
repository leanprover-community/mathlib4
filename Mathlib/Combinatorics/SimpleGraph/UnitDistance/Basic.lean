/-
Copyright (c) 2025 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Topology.MetricSpace.Defs

/-!
# Unit-distance graph embeddings

An embedding of a graph into some metric space is _unit-distance_ if the distance between any two
adjacent vertices is 1. The space in question is usually the Euclidean plane, but can also be
higher-dimensional Euclidean space or the sphere (cf. [Frankl_2020]). We do not require nonadjacent
vertices to not be distance 1 apart as [hong2014] does.

## Main definitions

* `G.UnitDistEmbedding E` is a unit-distance embedding of `G` into `E`.
* `UnitDistEmbedding.copy`, `UnitDistEmbedding.embed`, `UnitDistEmbedding.iso`: transfer a
  unit-distance embedding down a `Copy`, graph embedding or graph isomorphism respectively.
-/

@[expose] public section

namespace SimpleGraph

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} {E : Type*} [MetricSpace E]

variable (G E) in
/-- A unit-distance embedding of a graph into a metric space is a vertex embedding
such that adjacent vertices are at distance 1 from each other. -/
structure UnitDistEmbedding where
  /-- The embedding itself (position of vertices) -/
  p : V ↪ E
  /-- The distance between any two adjacent vertices is 1. -/
  unit_dist {u v} (ha : G.Adj u v) : dist (p u) (p v) = 1

namespace UnitDistEmbedding

variable (U : G.UnitDistEmbedding E)

/-- Derive a unit-distance embedding of `H` from a unit-distance embedding of `G` containing `H`. -/
def copy (f : H.Copy G) : H.UnitDistEmbedding E where
  p := f.toEmbedding.trans U.p
  unit_dist ha := U.unit_dist (f.toHom.map_adj ha)

/-- `U.copy` specialised to graph embeddings. -/
def embed (emb : H ↪g G) : H.UnitDistEmbedding E :=
  U.copy emb.toCopy

/-- Transfer a unit-distance embedding across a graph isomorphism. -/
def iso (e : G ≃g H) : H.UnitDistEmbedding E :=
  U.copy e.symm.toCopy

end UnitDistEmbedding

end SimpleGraph
