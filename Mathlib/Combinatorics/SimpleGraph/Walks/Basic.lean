/-
Copyright (c) 2021 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Peter Nelson
-/
module

public import Mathlib.Combinatorics.SimpleGraph.GraphLike
public import Mathlib.Combinatorics.GraphLike.Walks.Prod

/-!
# Walks

In a simple graph, a *walk* is a finite sequence of adjacent vertices, and can be
thought of equally well as a sequence of directed edges.

**Warning:** graph theorists mean something different by "path" than
do homotopy theorists.  A "walk" in graph theory is a "path" in
homotopy theory.  Another warning: some graph theorists use "path" and
"simple path" for "walk" and "path."

Some definitions and theorems have inspiration from multigraph
counterparts in [Chou1994].

## Main definitions

* `SimpleGraph.Walk.edges`: The list of edges a walk visits in order
* `SimpleGraph.Walk.edgeSet`: The set of edges of a walk visits

## Tags
walks
-/

@[expose] public section

open SimpleGraph DartLike SymmDartLike GraphLike SymmGraphLike
namespace GraphLike

universe u
variable {V : Type u} (G : SimpleGraph V) {u v w : V}

/-- The one-edge walk associated to a pair of adjacent vertices. -/
@[match_pattern, reducible]
def Adj.toWalk {G : SimpleGraph V} {u v : V} (h : G.Adj u v) : Walk G u v :=
  Walk.cons (Adj.toStep h) Walk.nil

namespace Walk

variable {G}

/-- The `edges` of a walk is the list of edges it visits in order.
This is defined to be the list of edges underlying `SimpleGraph.Walk.darts`. -/
def edges {u v : V} (p : Walk G u v) : List (Sym2 V) := p.darts.map dartSym2

/-- Every edge in a walk's edge list is an edge of the graph.
It is written in this form (rather than using `⊆`) to avoid unsightly coercions. -/
theorem edges_subset_edgeSet {u v} : ∀ (p : Walk G u v) ⦃e : Sym2 V⦄, e ∈ p.edges → e ∈ G.edgeSet
  | cons h' p', e, h => by
    cases h
    · exact h'.prop.1
    next h' => exact edges_subset_edgeSet p' h'

theorem adj_of_mem_edges {u v x y : V} (p : Walk G u v) (h : s(x, y) ∈ p.edges) : G.Adj x y :=
  p.edges_subset_edgeSet h

@[simp]
theorem edges_nil {u : V} : (nil : Walk G u u).edges = [] := rfl

@[simp]
theorem edges_cons {u v w : V} (s : step G u v) (p : Walk G v w) :
    (cons s p).edges = s(u, v) :: p.edges := by simp [edges]

@[simp, grind =]
theorem length_edges {u v : V} (p : Walk G u v) : p.edges.length = p.length := by simp [edges]

theorem mem_support_iff_exists_mem_edges {u v w : V} {p : Walk G u v} :
    w ∈ p.support ↔ w = v ∨ ∃ e ∈ p.edges, w ∈ e := by
  induction p <;> aesop

theorem edges_eq_zipWith_support {u v : V} {p : Walk G u v} :
    p.edges = List.zipWith (s(·, ·)) p.support p.support.tail := by
  induction p with
  | nil => simp
  | cons _ p' ih => cases p' <;> simp [edges_cons, ih]

theorem edges_injective {u v : V} : Function.Injective (Walk.edges : Walk G u v → List (Sym2 V))
  | .nil, .nil, _ => rfl
  | .nil, .cons _ _, h => by simp at h
  | .cons _ _, .nil, h => by simp at h
  | .cons' u v c h₁ w₁, .cons' _ v' _ h₂ w₂, h => by
    have h₃ : u ≠ v' := by rintro rfl; exact G.loopless.irrefl _ h₂.adj
    obtain ⟨rfl, h₃⟩ : v = v' ∧ w₁.edges = w₂.edges := by simpa [h₁.adj, h₃] using h
    rw [edges_injective h₃, Subsingleton.elim h₁ h₂]

/-- The `Set` of edges of a walk. -/
def edgeSet {u v : V} (p : Walk G u v) : Set (Sym2 V) := {e | e ∈ p.edges}

@[simp]
lemma mem_edgeSet {u v : V} {p : Walk G u v} {e : Sym2 V} : e ∈ p.edgeSet ↔ e ∈ p.edges := Iff.rfl

@[simp]
lemma edgeSet_nil (u : V) : (nil : Walk G u u).edgeSet = ∅ := by ext; simp

@[simp]
theorem edgeSet_cons {u v w : V} (s : step G u v) (p : Walk G v w) :
    (cons s p).edgeSet = insert s(u, v) p.edgeSet := by ext; simp

theorem coe_edges_toFinset [DecidableEq V] {u v : V} (p : Walk G u v) :
    (p.edges.toFinset : Set (Sym2 V)) = p.edgeSet := by
  simp [edgeSet]

@[simp]
lemma edges_eq_nil {p : Walk G v w} : p.edges = [] ↔ p.Nil := by
  cases p <;> simp

lemma nil_of_subsingleton [Subsingleton V] (p : Walk G v w) : p.Nil :=
  match p with
  | nil => Nil.nil
  | cons s w => (Unique.eq_default G ▸ s).adj |>.elim

theorem mem_support_iff_exists_mem_edges_of_not_nil {u v w : V} {p : Walk G u v} (hnil : ¬p.Nil) :
    w ∈ p.support ↔ ∃ e ∈ p.edges, w ∈ e := by
  induction p with
  | nil => simp at hnil
  | cons h p ih => cases p <;> aesop

end GraphLike.Walk
