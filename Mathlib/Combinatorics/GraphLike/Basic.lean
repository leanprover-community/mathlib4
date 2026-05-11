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
  rw [← exists_darts_iff_adj] at h
  obtain ⟨d, hd, rfl, rfl⟩ := h
  exact source_mem_of_darts hd

lemma Adj.right_mem (h : Adj G v w) : w ∈ V(G) := by
  rw [← exists_darts_iff_adj] at h
  obtain ⟨d, hd, rfl, rfl⟩ := h
  exact target_mem_of_darts hd

/-- Convert a dart to a pair of vertices. -/
@[expose] def toProd (d : D(G)) : V × V := (source G d.val, target G d.val)

/-- The step from `u` to `v` is a dart from `u` to `v`. -/
@[expose]
def Step (G : Gr) [GraphLike V D E Gr] (u v : V) : Type _ :=
  {d : D // d ∈ D(G) ∧ source G d = u ∧ target G d = v}

instance [DecidableEq D] : DecidableEq (Step G u v) := Subtype.instDecidableEq

@[simp]
lemma Step.source (h : Step G u v) : source G h.val = u := by
  obtain ⟨d, hd, hu, hv⟩ := h
  exact hu

@[simp]
lemma Step.target (h : Step G u v) : target G h.val = v := by
  obtain ⟨d, hd, hu, hv⟩ := h
  exact hv

lemma Step.source_mem (h : Step G u v) : u ∈ V(G) := by
  obtain ⟨d, hd, rfl, rfl⟩ := h
  exact source_mem_of_darts hd

lemma Step.target_mem (h : Step G u v) : v ∈ V(G) := by
  obtain ⟨d, hd, rfl, rfl⟩ := h
  exact target_mem_of_darts hd

lemma Step.source_eq_of_val_eq {s₁ : Step G u v} {s₂ : Step G u' v'} (h : s₁.val = s₂.val) :
    u = u' := by
  obtain ⟨d₁, hd₁, rfl, rfl⟩ := s₁
  obtain ⟨d₂, hd₂, rfl, rfl⟩ := s₂
  obtain rfl : d₁ = d₂ := h
  rfl

lemma Step.target_eq_of_val_eq {s₁ : Step G u v} {s₂ : Step G u' v'} (h : s₁.val = s₂.val) :
    v = v' := by
  obtain ⟨d₁, hd₁, rfl, rfl⟩ := s₁
  obtain ⟨d₂, hd₂, rfl, rfl⟩ := s₂
  obtain rfl : d₁ = d₂ := h
  rfl

@[ext] lemma Step.ext {s₁ s₂ : Step G u v} (h : s₁.val = s₂.val) : s₁ = s₂ := Subtype.ext h

attribute [simp] Step.ext_iff

@[simp]
lemma Step.ext_HEq {u' v'} {s₁ : Step G u v} {s₂ : Step G u' v'} (h : s₁.val = s₂.val) :
    s₁ ≍ s₂ := by
  obtain ⟨d₁, hd₁, rfl, rfl⟩ := s₁
  obtain ⟨d₂, hd₂, rfl, rfl⟩ := s₂
  obtain rfl : d₁ = d₂ := h
  rfl

/-- Convert a step to a dart. -/
@[expose] def Step.todart (h : Step G u v) : D(G) := ⟨h.val, h.prop.1⟩

lemma Step.val_todart (h : Step G u v) : h.todart.val = h.val := by simp [Step.todart]

lemma Step.source_todart (s : Step G u v) : GraphLike.source G s.todart.val = u := by
  obtain ⟨d, hd, rfl, rfl⟩ := s
  rfl

lemma Step.target_todart (s : Step G u v) : GraphLike.target G s.todart.val = v := by
  obtain ⟨d, hd, rfl, rfl⟩ := s
  rfl

lemma Step.adj (h : Step G u v) : Adj G u v := by
  rw [← exists_darts_iff_adj]
  obtain ⟨d, hd, rfl, rfl⟩ := h
  exact ⟨d, hd, rfl, rfl⟩

/-- If `u` and `v` are adjacent, then there exists a step from `u` to `v`. -/
noncomputable def Adj.toStep (h : Adj G u v) : Step G u v :=
  ⟨(exists_darts_iff_adj.mpr h).choose, (exists_darts_iff_adj.mpr h).choose_spec⟩

lemma Adj.adj_toStep (h : Adj G u v) : (h.toStep).adj = h := rfl

/-- Convert a dart to a step. -/
@[expose] def dartStep (d : D(G)) : Step G (source G d.val) (target G d.val) :=
  ⟨d.val, d.prop, rfl, rfl⟩

@[simp]
lemma val_dartStep (d : D(G)) : (dartStep d).val = d.val := by simp [dartStep]

/-- Two darts are said to be adjacent if they could be consecutive darts in a walk -- that is, the
first dart's target is equal to the second dart's source. -/
@[expose] def DartAdj (d d' : D(G)) : Prop := target G d.val = source G d'.val

end GraphLike.GraphLike
