/-
Copyright (c) 2026 Tianyi Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianyi Zhao
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Walk.Basic

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

variable {V : Type*} {G : SimpleGraph V} {u v w : V}

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

@[grind →] theorem IsChordless.mem_edges {p : G.Walk u v} (h : p.IsChordless) {u' v' : V}
    (hu' : u' ∈ p.support) (hv' : v' ∈ p.support) (hadj : G.Adj u' v') : s(u', v') ∈ p.edges :=
  isChordless_iff_forall_mem_edges.mp h hu' hv' hadj

end Walk
end SimpleGraph
