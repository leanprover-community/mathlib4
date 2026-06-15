/-
Copyright (c) 2026 metakunt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: metakunt
-/
module

public import Mathlib.Data.Sym.Sym2


/-!
## Mixed graphs
Work in progress.

## Main definitions
* `EdgeOrientation` A directed or undirected edge
* `IsStep` whether an edge `e` can be stepped from `a` to `b`
* `support` the endpoints corresponding to an edge
* `IsLoop` Whether an edge is a loop
* `MixedGraph` The generalisation of a `Graph`
TODO: Other definitions will be extracted in their own files.

-/

@[expose] public section

/-- Orientation of the edge for a mixed graph -/
inductive EdgeOrientation (α : Type*) where
  /- Directed edge -/
  | directed (s t : α)
  /- Undirected edge -/
  | undirected (e : Sym2 α)

namespace EdgeOrientation

variable {α : Type*}

/-- Whether a given edge is undirected. -/
def IsUndirected : EdgeOrientation α → Prop
  | directed _ _ => False
  | undirected _ => True

/-- Directed link for a mixed graph -/
def IsStep : EdgeOrientation α → α → α → Prop
  | directed a b, c, d => a = c ∧ b = d
  | undirected e, c, d => e = .mk c d

/-- The vertices for a given edge. -/
def support : EdgeOrientation α → Sym2 α
  | directed s t => .mk s t
  | undirected e => e

/-- Reverses the edge. -/
def reverse : EdgeOrientation α → EdgeOrientation α
  | directed s t => directed t s
  | undirected e => undirected e

@[simp]
lemma reverse_reverse (e : EdgeOrientation α) : e.reverse.reverse = e := by
  simp only [reverse]
  grind

lemma reverse_support (e : EdgeOrientation α) : e.reverse.support = e.support := by
  cases e <;> grind [reverse, support]

/-- `IsLoop e` means that the edge `e` is a loop. -/
def IsLoop (e : EdgeOrientation α) := e.support.IsDiag

lemma isLoop_of_directed_iff_eq {a b : α} : (EdgeOrientation.directed a b).IsLoop ↔ a = b := by
  grind [support, IsLoop, Sym2.mk_isDiag_iff]


lemma isLoop_iff {e : EdgeOrientation α} : e.IsLoop ↔ ∃ a : α,
    e = .directed a a ∨ e = .undirected (.diag a) := by
  match e with
  | undirected a =>
    constructor
    · exact fun x => ⟨ a.diagElem x , by simp ⟩
    · simp only [reduceCtorEq, undirected.injEq, false_or, forall_exists_index]
      exact fun x y => by simp [y, IsLoop, support]
  | directed a b =>
    constructor
    · exact fun h => ⟨ a, by simp [isLoop_of_directed_iff_eq.mp h] ⟩
    · grind [isLoop_of_directed_iff_eq]


end EdgeOrientation


/-- Mixed graphs, as a set of vertices and a bundled function that derives the edges. -/
structure MixedGraph (α β : Type*) where
  /-- The vertex set. -/
  vertexSet : Set α
  /-- Bundled function deriving the edges. -/
  edgeOrientation : β → Option (EdgeOrientation α)
  /-- The support of an edge must be contained in the vertex set. -/
  is_compatible_edge : ∀ (b : β) (h : (edgeOrientation b).isSome),
    ((edgeOrientation b).get h).support ∈ Sym2.fromRel
    (r := fun a b => a ∈ vertexSet ∧ b ∈ vertexSet) (by grind [Std.Symm.mk])


namespace MixedGraph

universe u v
variable {α : Type u} {β : Type v} (G H : MixedGraph α β)

/-- The set of edges, this can't be part of the structure as it otherwise could be overridden. -/
def edgeSet := G.edgeOrientation ⁻¹' {x | x.isSome}

lemma edgeSet_not_mem_iff_none (e : β) : e ∉ G.edgeSet ↔ G.edgeOrientation e = none  := by
  simp [edgeSet]

/-- Given an edge `b` returns the edge orientation. -/
def get {b : β} (h : b ∈ G.edgeSet) : EdgeOrientation α :=
  (G.edgeOrientation b).get (by grind [edgeSet])

/-- A mixed graph is undirected if all edges are undirected. -/
def IsUndirected : Prop :=
  ∀e, (h : e ∈ G.edgeSet) → (G.get h).IsUndirected

/-- Restricts a graph to a subset, analogous to `Graph.restrict`. -/
def restrict (b : Set β) [DecidablePred (· ∈ b)] : MixedGraph α β where
  vertexSet := G.vertexSet
  edgeOrientation := b.piecewise (G.edgeOrientation) (fun _ => .none)
  is_compatible_edge e h := by
    have hl : e ∈ b := by
      by_contra! hcon
      simp [hcon] at h
    have ce3 := Set.piecewise_eq_of_mem b (G.edgeOrientation) (fun _ ↦ none) hl
    have ce := G.is_compatible_edge e (by grind)
    grind

/-- Deletes edges from a graph, analogous to `Graph.deleteEdges`. -/
def deleteEdges (b : Set β) [DecidablePred (· ∈ b)] : MixedGraph α β where
  vertexSet := G.vertexSet
  edgeOrientation := b.piecewise (fun _ => .none) (G.edgeOrientation)
  is_compatible_edge e h := by
    have hl : e ∉ b := by
      by_contra! hcon
      simp [hcon] at h
    have ce3 := Set.piecewise_eq_of_notMem b (fun _ ↦ none) (G.edgeOrientation)  hl
    have ce := G.is_compatible_edge e (by grind)
    grind


theorem delete_edges_eq_restrict_diff (b : Set β) [DecidablePred (· ∈ b)]
    [DecidablePred (· ∈ G.edgeSet)] : G.deleteEdges b = G.restrict (G.edgeSet \ b) := by
  simp only [deleteEdges, restrict, mk.injEq, true_and]
  ext e f
  by_cases h : e ∈ b
  · simp [h]
  · by_cases h2 : e ∈ G.edgeSet
    · simp only [h, not_false_eq_true, Set.piecewise_eq_of_notMem]
      suffices hh : e ∈ G.edgeSet \ b by simp [hh]
      grind
    · simp only [h, not_false_eq_true, Set.piecewise_eq_of_notMem, Set.mem_sdiff, h2, and_true,
      reduceCtorEq, iff_false]
      suffices G.edgeOrientation e = none by grind
      grind [edgeSet_not_mem_iff_none]

/-- Analogous to `Graph.IsSubgraph`. -/
structure IsSubgraph (H G : MixedGraph α β) where
  vertexSet_mono : H.vertexSet ⊆ G.vertexSet
  edges_eq : ∀ e ∈ H.edgeSet, H.edgeOrientation e = G.edgeOrientation e

theorem subgraph_delete_edges {b : Set β} [DecidablePred (· ∈ b)] :
    IsSubgraph (G.deleteEdges b) G := by
  apply IsSubgraph.mk
  · simp [deleteEdges]
  · simp only [edgeSet, deleteEdges, Set.preimage_setOf_eq, Set.mem_setOf_eq]
    intro e he
    by_cases hc : e ∈ b <;> simp [hc] at *


/-- Two graphs are compatible if the orientation of the intersection of their edge sets
    coincide. -/
def Compatible := ∀ e ∈ G.edgeSet ∩ H.edgeSet, G.edgeOrientation e = H.edgeOrientation e

/-- Mixed walk, analogous to `SimpleGraph.Walk`. -/
inductive Walk (G : MixedGraph α β) : α → α → Type max u v
  | nil (a : α) : Walk G a a
  | cons {a b c : α} (e : β) (h : e ∈ G.edgeSet)
    (p: Walk G a b) (h : EdgeOrientation.IsStep (G.get h) b c) : Walk G a c

end MixedGraph
