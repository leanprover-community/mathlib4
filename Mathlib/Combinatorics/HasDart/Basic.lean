/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Mathlib.Logic.Function.Basic

/-!
# Typeclass for different kinds of graphs

This module defines the typeclass `HasDart` for capturing the common structure of different kinds of
graph structures including `SimpleGraph`, `Graph`, and `Digraph`.

## Main definitions

* `HasDart`: is the main typeclass for capturing the common structure of graph-like structures.
  The field `verts` gives the set of vertices of a graph-like structure,
  the field `dart` gives the type of darts, which is an oriented edge, of a graph-like structure,
  and the field `Adj` gives the adjacency relation between vertices.

## TODO
* Migrate from `SimpleGraph` all the results that only depend on the adjacency relation.

-/

@[expose] public section

universe u'

class HasDart (α : outParam Type*) (Gr : Type*) where
  verts (G : Gr) : Set α
  dart : Gr → α → α → Sort u'
  Adj (G : Gr) (u v : α) : Prop := Nonempty (dart G u v)
  adj_iff_nonempty_dart {G : Gr} {u v : α} : Adj G u v ↔ Nonempty (dart G u v) := by rfl
  left_mem_verts_of_adj {G : Gr} {u v : α} (h : Adj G u v) : u ∈ verts G
  right_mem_verts_of_adj {G : Gr} {u v : α} (h : Adj G u v) : v ∈ verts G

namespace HasDart

variable {α Gr : Type*} [HasDart α Gr] {G : Gr} {v w : α}

scoped notation "V(" G ")" => verts G

/-- Dot notation for reverse direction of `adj_iff_nonempty_dart`. -/
lemma dart.adj (d : dart G v w) : Adj G v w := adj_iff_nonempty_dart.mpr ⟨d⟩

/-- Dot notation for `left_mem_verts_of_adj`. -/
lemma Adj.left_mem (h : Adj G v w) : v ∈ V(G) :=
  left_mem_verts_of_adj h

/-- Dot notation for `right_mem_verts_of_adj`. -/
lemma Adj.right_mem (h : Adj G v w) : w ∈ V(G) :=
  right_mem_verts_of_adj h

lemma dart.left_mem (d : dart G v w) : v ∈ V(G) :=
  d.adj.left_mem

lemma dart.right_mem (d : dart G v w) : w ∈ V(G) :=
  d.adj.right_mem

end HasDart
