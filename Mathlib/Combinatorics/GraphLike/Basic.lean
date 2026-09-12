/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Mathlib.Data.Sym.Sym2

/-!
# Typeclass for different kinds of graphs

This module defines the typeclass `GraphLike` for capturing the common structure of different kinds
of graph structures including `SimpleGraph`, `Graph`, and `Digraph`.

## Main definitions

* `GraphLike`: is the main typeclass for capturing the common notion of graphs.
  The field `verts` gives the set of vertices of a graph-like structure,
  the field `darts` gives the set of darts, which is an oriented edge, of a graph-like structure,
  the field `edges` gives the set of edges of a graph-like structure,
  and the field `Adj` gives the adjacency relation between vertices.
* `NoMultiEdgeGraphLike`: is the typeclass for graph-like structures with no multi-edge.
* `darts G` is the direct generalization of `Dart` in `SimpleGraph`.

## Notes

* `GraphLike V D E Gr` generalizes `SimpleGraph`, `Digraph`, and `Graph`. When multi-digraph and
  hypergraphs are formalized, they can also use this typeclass.

-/

public section

/-- The `GraphLike` typeclass abstracts over graph-like structures including hypergraphs.
It has vertex and edge sets so subgraph relations can be handled within the same type.
The "darts" terminology comes from combinatorial maps, and they are also known as "half-edges" or
"bonds." They represents the ways an edge can be traversed: if `d` is a dart with `edge d = e`,
`source d = u` and `target d = v` then `d` is walk of length 1 from `u` to `v` with edge `e`. In an
undirected graph, each edge is composed of two darts.
`Adj` is the adjacency relation of a graph-like structure. Two vertices, `u` & `v`, are adjacent iff
there is a dart between them and therefore there is an edge that can be traversed from `u` to `v`.
(See `exists_darts_iff_adj`.) -/
class GraphLike (V D E : outParam Type*) (Gr : Type*) where
  /-- The set of vertices of a graph-like structure. -/
  verts : Gr → Set V
  /-- The set of darts (oriented edges) of a graph-like structure. -/
  darts : Gr → Set D
  /-- The set of edges of a graph-like structure. -/
  edges : Gr → Set E
  /-- The source vertex of a dart. -/
  source : Gr → D → V
  /-- The target vertex of a dart. -/
  target : Gr → D → V
  /-- The edge of a dart. -/
  edge : Gr → D → E
  source_mem_of_darts : ∀ ⦃G d⦄, d ∈ darts G → source G d ∈ verts G
  target_mem_of_darts : ∀ ⦃G d⦄, d ∈ darts G → target G d ∈ verts G
  edge_mem_of_darts : ∀ ⦃G d⦄, d ∈ darts G → edge G d ∈ edges G
  /-- The adjacency relation of a graph-like structure. -/
  Adj : Gr → V → V → Prop := fun G u v ↦ ∃ d ∈ darts G, source G d = u ∧ target G d = v
  /-- Two vertices are adjacent if and only if there is a dart between them. -/
  exists_darts_iff_adj : ∀ ⦃G u v⦄, (∃ d ∈ darts G, source G d = u ∧ target G d = v) ↔ Adj G u v

namespace GraphLike

@[inherit_doc verts]
scoped notation "V(" G ")" => verts G

@[inherit_doc darts]
scoped notation "D(" G ")" => darts G

@[inherit_doc edges]
scoped notation "E(" G ")" => edges G

variable {V D E Gr : Type*} {G : Gr} {u u' v v' w : V} {d : D} {e : E}

section GraphLike

variable [GraphLike V D E Gr]

@[ext] theorem darts_ext (d₁ d₂ : D(G)) (h : d₁.val = d₂.val) : d₁ = d₂ := Subtype.ext h

lemma adj_source_target (hd : d ∈ D(G)) : Adj G (source G d) (target G d) :=
  exists_darts_iff_adj.mp ⟨d, hd, rfl, rfl⟩

lemma Adj.left_mem (h : Adj G v w) : v ∈ V(G) := by
  obtain ⟨d, hd, rfl, rfl⟩ := exists_darts_iff_adj.mpr h
  exact source_mem_of_darts hd

lemma Adj.right_mem (h : Adj G v w) : w ∈ V(G) := by
  obtain ⟨d, hd, rfl, rfl⟩ := exists_darts_iff_adj.mpr h
  exact target_mem_of_darts hd

/-- Convert a dart to a pair of vertices. -/
@[expose] def toProd (d : D(G)) : V × V := (source G d.val, target G d.val)

/-- Two darts are said to be adjacent if they could be consecutive darts in a walk -- that is, the
first dart's target is equal to the second dart's source. -/
@[expose] def DartAdj (d d' : D(G)) : Prop := target G d.val = source G d'.val

end GraphLike

section noMultiEdgeGraphLike

/-
### GraphLike with no multi-edge

Some graph-like structures, such as `SimpleGraph` and `Digraph`, does not allow multiple darts/edges
between the same pair of vertices. This section defines a typeclass `NoMultiEdgeGraphLike` for such
graph-like structures.
-/

/-- A graph-like structure with no multi-edge. This includes `SimpleGraph` and `Digraph`. -/
class NoMultiEdgeGraphLike (V D E : outParam Type*) (Gr : Type*) extends GraphLike V D E Gr where
  protected src_tgt_inj (G : Gr) : Function.Injective (fun d ↦ (source G d, target G d))

variable [NoMultiEdgeGraphLike V D E Gr]

lemma dart_eq_of_src_tgt_eq {d₁ d₂ : D} (h : source G d₁ = source G d₂)
    (h' : target G d₁ = target G d₂) : d₁ = d₂ := by
  apply NoMultiEdgeGraphLike.src_tgt_inj G
  grind

lemma src_tgt_inj (d₁ d₂ : D) : source G d₁ = source G d₂ ∧ target G d₁ = target G d₂ ↔ d₁ = d₂ :=
  ⟨fun h => dart_eq_of_src_tgt_eq h.1 h.2, by grind⟩

@[simp]
lemma mem_darts_iff_adj : d ∈ darts G ↔ Adj G (source G d) (target G d) := by
  rw [← exists_darts_iff_adj]
  refine ⟨fun h => (by use d), fun ⟨d', hd', hs, ht⟩ => ?_⟩
  obtain rfl := src_tgt_inj d' d |>.mp ⟨hs, ht⟩
  exact hd'

instance [DecidableRel (Adj G)] : DecidablePred (· ∈ darts G) :=
  fun d => decidable_of_iff (Adj G (source G d) (target G d)) mem_darts_iff_adj.symm

end noMultiEdgeGraphLike
end GraphLike
