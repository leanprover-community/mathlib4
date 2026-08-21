/-
Copyright (c) 2026 Tianyi Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianyi Zhao
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.Walk.Maps

/-!
# Chords of walks

This file defines chords and chordless walks in a simple graph.

## Main definitions

* `SimpleGraph.Walk.IsChord`: an edge of the ambient graph between two vertices of a walk
  which is not an edge of the walk itself
* `SimpleGraph.Walk.IsChordless`: a walk with no chords

## Tags
walks, chords
-/

public section

namespace SimpleGraph
namespace Walk

variable {V V' : Type*} {G : SimpleGraph V} {G' : SimpleGraph V'} {u v w a b : V} {p : G.Walk u v}

/-- A chord of a walk `p` is an edge of `G` between two vertices of `p` which is not one
of the edges of `p`. -/
@[expose]
def IsChord (p : G.Walk u v) (e : Sym2 V) : Prop :=
  e ∈ G.edgeSet ∧ e ∉ p.edges ∧
    e.lift ⟨fun v w => v ∈ p.support ∧ w ∈ p.support, by grind⟩

theorem isChord_sym2Mk {p : G.Walk u v} {u' v' : V} :
    p.IsChord s(u', v') ↔ G.Adj u' v' ∧ s(u', v') ∉ p.edges ∧ u' ∈ p.support ∧ v' ∈ p.support :=
  .rfl

/-- A walk is chordless if it has no chords. -/
@[expose]
def IsChordless (p : G.Walk u v) : Prop :=
  ∀ ⦃e : Sym2 V⦄, ¬ p.IsChord e

theorem isChordless_iff_forall_mem_edges {p : G.Walk u v} :
    p.IsChordless ↔
      ∀ ⦃u' v' : V⦄, u' ∈ p.support → v' ∈ p.support → G.Adj u' v' → s(u', v') ∈ p.edges := by
  simp [IsChordless, Sym2.forall, isChord_sym2Mk]; grind

theorem IsChordless.mem_edges {p : G.Walk u v} (h : p.IsChordless) {u' v' : V}
    (hu' : u' ∈ p.support) (hv' : v' ∈ p.support) (hadj : G.Adj u' v') : s(u', v') ∈ p.edges :=
  isChordless_iff_forall_mem_edges.mp h hu' hv' hadj

theorem _root_.SimpleGraph.Adj.isChordless_toWalk (h : G.Adj u v) : h.toWalk.IsChordless := by
  grind [isChordless_iff_forall_mem_edges, h.support_toWalk, h.edges_toWalk, Adj.ne]

protected theorem IsChord.map (f : Copy G G') (hp : p.IsChord s(a, b)) :
    (p.map f.toHom).IsChord s(f a, f b) := by
  simp_rw [IsChord, support_map, edges_map]
  refine ⟨f.toHom.map_adj hp.left, fun h ↦ hp.right.left ?_, ?_, ?_⟩
  · exact (List.mem_map_of_injective <| Sym2.map.injective f.injective).mp h
  · exact List.mem_map_of_mem hp.right.right.left
  · exact List.mem_map_of_mem hp.right.right.right

protected theorem IsChord.of_map {f : G ↪g G'} (hp : (p.map f.toHom).IsChord s(f a, f b)) :
    p.IsChord s(a, b) := by
  rcases hp with ⟨hadj, hp, ha, hb⟩
  refine ⟨f.map_adj_iff.mp hadj, fun h ↦ hp ?_, ?_, ?_⟩
  · rw [edges_map]
    exact List.mem_map_of_mem h
  · simpa using ha
  · simpa using hb

theorem isChord_map_iff {f : G ↪g G'} : (p.map f.toHom).IsChord s(f a, f b) ↔ p.IsChord s(a, b) :=
  ⟨.of_map, .map f.toCopy⟩

protected theorem IsChordless.map (f : G ↪g G') (hp : p.IsChordless) :
    (p.map f.toHom).IsChordless := by
  refine Sym2.ind fun a b he ↦ ?_
  have ⟨_, _, ha, hb⟩ := he
  rw [support_map, List.mem_map] at ha hb
  rcases ha, hb with ⟨⟨a, _, rfl⟩, ⟨b, _, rfl⟩⟩
  exact hp <| isChord_map_iff.mp he

protected theorem IsChordless.of_map {f : Copy G G'} (hp : (p.map f.toHom).IsChordless) :
    p.IsChordless :=
  Sym2.ind fun _ _ h ↦ hp <| h.map f

theorem isChordless_map_iff {f : G ↪g G'} : (p.map f.toHom).IsChordless ↔ p.IsChordless :=
  ⟨.of_map (f := f.toCopy), .map f⟩

end Walk
end SimpleGraph
