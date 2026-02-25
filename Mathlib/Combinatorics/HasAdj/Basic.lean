/-
Copyright (c) 2026 Iván Renison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iván Renison
-/
module

public import Batteries.Data.List.Basic
public import Mathlib.Data.Rel

/-!
# Typeclass for different kinds of (simple) graphs

This module defines the typeclass `HasAdj` for capturing the common structure of different kinds of
(simple) graphs.

## Main definitions

* `HasAdj`: is the main typeclass in question. The field `verts` gives the set of vertices of a
  graph, and the field `Adj` gives the adjacency relation between vertices.

## TODO
* Migrate from `SimpleGraph` all the results that only depend on the adjacency relation.

-/

@[expose] public section

/-- Typeclass for (simple) graphs. -/
class HasAdj (α : outParam Type*) (Gr : Type*) where
  /-- The set of vertices of the graph. -/
  verts (G : Gr) : Set α
  /-- The adjacency relation of the graph. -/
  Adj (G : Gr) : α → α → Prop
  /-- There is no edge of the graph outside of it vertices. -/
  left_mem_verts_of_adj {G : Gr} {v w : α} (h : Adj G v w) : v ∈ verts G
  /-- There is no edge of the graph outside of it vertices. -/
  right_mem_verts_of_adj {G : Gr} {v w : α} (h : Adj G v w) : w ∈ verts G

namespace HasAdj

variable {Gr : Type*} {α : Type*} [HasAdj α Gr]

/-- Dot notation for `left_mem_verts_of_adj`. -/
lemma Adj.left_mem_verts {G : Gr} {v w : α} (h : Adj G v w) : v ∈ verts G :=
  left_mem_verts_of_adj h

/-- Dot notation for `right_mem_verts_of_adj`. -/
lemma Adj.right_mem_verts {G : Gr} {v w : α} (h : Adj G v w) : w ∈ verts G :=
  right_mem_verts_of_adj h

end HasAdj
