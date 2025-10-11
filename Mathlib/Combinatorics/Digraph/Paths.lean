/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Mathlib.Combinatorics.Digraph.Walk
import Mathlib.Combinatorics.Digraph.WalkDecomp

/-!
# Trails, Paths, Circuits, and Cycles in Digraphs

This file defines trails, paths, circuits, and cycles in directed graphs.

In a digraph,

* A *trail* is a walk whose edges (arcs) each appear no more than once.

* A *circuit* is a nonempty trail whose first and last vertices are the same.

* A *path* is a trail whose vertices appear no more than once.

* A *cycle* is a nonempty trail whose first and last vertices are the same and whose vertices
  except for the first appear no more than once.

* A *strong walk* exists between two vertices if there are walks in both directions between them.

* A *weak walk* exists between two vertices if there is a walk between them in the underlying
  undirected graph.

## Main definitions

* `Digraph.Walk.IsTrail`, `Digraph.Walk.IsPath`, `Digraph.Walk.IsCircuit`, and `Digraph.Walk.IsCycle`.

* `Digraph.Path` - A structure representing a path in a digraph.

* `Digraph.Reachable`, `Digraph.WeaklyReachable`, and `Digraph.StronglyReachable` - Relations
  describing connectivity in digraphs.

* `Digraph.Connected`, `Digraph.WeaklyConnected`, and `Digraph.StronglyConnected` - Predicates
  for different types of connectivity of digraphs.

## Implementation notes

The implementation closely follows the structure of `SimpleGraph.Path`, but accounts for the
directional nature of edges in digraphs.
-/

open Function

universe u v w

namespace Digraph

variable {V : Type u} {V' : Type v} {V'' : Type w}
variable (G : Digraph V) (G' : Digraph V')

namespace Walk

variable {G} {u v w : V}

/-! ### Trails, paths, circuits, cycles -/

/-- A *trail* is a walk with no repeating edges. -/
@[mk_iff isTrail_def]
structure IsTrail {u v : V} (p : G.Walk u v) : Prop where
  /-- The edges in the trail must not repeat -/
  edges_nodup : p.darts.Nodup

/-- A *path* is a walk with no repeating vertices.
Use `Digraph.Walk.IsPath.mk'` for a simpler constructor. -/
structure IsPath {u v : V} (p : G.Walk u v) : Prop extends IsTrail p where
  /-- The vertices in the path must not repeat -/
  support_nodup : p.support.Nodup

protected lemma IsPath.isTrail {p : Walk G u v} (h : IsPath p) : IsTrail p := h.toIsTrail

/-- A *circuit* at `u : V` is a nonempty trail beginning and ending at `u`. -/
@[mk_iff isCircuit_def]
structure IsCircuit {u : V} (p : G.Walk u u) : Prop extends IsTrail p where
  /-- A circuit is not the empty walk -/
  ne_nil : p ≠ nil

protected lemma IsCircuit.isTrail {p : Walk G u u} (h : IsCircuit p) : IsTrail p := h.toIsTrail

/-- A *cycle* at `u : V` is a circuit at `u` whose only repeating vertex
is `u` (which appears exactly twice). -/
structure IsCycle {u : V} (p : G.Walk u u) : Prop extends IsCircuit p where
  /-- The only vertex that can appear more than once in a cycle is the start/end vertex -/
  support_nodup : p.support.tail.Nodup

protected lemma IsCycle.isCircuit {p : Walk G u u} (h : IsCycle p) : IsCircuit p := h.toIsCircuit

@[simp]
theorem isTrail_copy {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v') :
    (p.copy hu hv).IsTrail ↔ p.IsTrail := by
  subst_vars
  rfl

theorem IsPath.mk' {u v : V} {p : G.Walk u v} (h : p.support.Nodup) : p.IsPath :=
  ⟨⟨edges_nodup_of_support_nodup h⟩, h⟩
  where
    /-- If no vertex repeats in a walk, then no edge repeats either. -/
    edges_nodup_of_support_nodup {u v : V} {p : G.Walk u v} (h : p.support.Nodup) : p.darts.Nodup := by
      induction p with
      | nil => simp [darts]
      | cons ha p ih =>
        simp [darts_cons]
        constructor
        · intro hm
          have hs : a ∈ p.support := by simpa using hm
          simp [support_cons] at h
          exact List.nodup_cons.1 h |>.1 hs
        · apply ih
          simp [support_cons] at h
          exact List.nodup_cons.1 h |>.2

theorem isPath_def {u v : V} (p : G.Walk u v) : p.IsPath ↔ p.support.Nodup :=
  ⟨IsPath.support_nodup, IsPath.mk'⟩

@[simp]
theorem isPath_copy {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v') :
    (p.copy hu hv).IsPath ↔ p.IsPath := by
  subst_vars
  rfl

@[simp]
theorem isCircuit_copy {u u'} (p : G.Walk u u) (hu : u = u') :
    (p.copy hu hu).IsCircuit ↔ p.IsCircuit := by
  subst_vars
  rfl

lemma IsCircuit.not_nil {p : G.Walk v v} (hp : IsCircuit p) : ¬p.Nil := fun h => hp.ne_nil (nil_iff_length_eq.2 ⟨rfl, h⟩).2

theorem isCycle_def {u : V} (p : G.Walk u u) :
    p.IsCycle ↔ p.IsTrail ∧ p ≠ nil ∧ p.support.tail.Nodup :=
  Iff.intro (fun h => ⟨h.1.1, h.1.2, h.2⟩) fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩

@[simp]
theorem isCycle_copy {u u'} (p : G.Walk u u) (hu : u = u') :
    (p.copy hu hu).IsCycle ↔ p.IsCycle := by
  subst_vars
  rfl

lemma IsCycle.not_nil {p : G.Walk v v} (hp : IsCycle p) : ¬p.Nil := hp.ne_nil ·.eq_nil

@[simp]
theorem IsTrail.nil {u : V} : (nil : G.Walk u u).IsTrail := ⟨by simp [darts]⟩

theorem IsTrail.of_cons {u v w : V} {h : G.Adj u v} {p : G.Walk v w} :
    (cons h p).IsTrail → p.IsTrail := by
  intro h'
  simp [isTrail_def, darts_cons] at h' ⊢
  exact h'.2

@[simp]
theorem cons_isTrail_iff {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    (cons h p).IsTrail ↔ p.IsTrail ∧ (u, v) ∉ p.darts := by
  simp [isTrail_def, darts_cons, and_comm]

theorem IsTrail.append {u v w : V} {p : G.Walk u v} {q : G.Walk v w}
    (hp : p.IsTrail) (hq : q.IsTrail) (h_disjoint : Disjoint p.darts q.darts) :
    (p.append q).IsTrail := by
  simp [isTrail_def, darts_append]
  constructor
  · exact List.nodup_append.2 ⟨hp.1, hq.1, h_disjoint⟩

theorem IsTrail.of_append_left {u v w : V} {p : G.Walk u v} {q : G.Walk v w}
    (h : (p.append q).IsTrail) : p.IsTrail := by
  simp [isTrail_def, darts_append] at h ⊢
  exact List.nodup_append_left h

theorem IsTrail.of_append_right {u v w : V} {p : G.Walk u v} {q : G.Walk v w}
    (h : (p.append q).IsTrail) : q.IsTrail := by
  simp [isTrail_def, darts_append] at h ⊢
  exact List.nodup_append_right h

theorem IsTrail.of_takeUntil [DecidableEq V] {u v w : V} {p : G.Walk v w} (h : p.IsTrail)
    (hw : u ∈ p.support) : (p.takeUntil u hw).IsTrail := by
  simp [isTrail_def] at h ⊢
  exact List.nodup_of_sublist (darts_takeUntil_subset _ _) h

theorem IsTrail.of_dropUntil [DecidableEq V] {u v w : V} {p : G.Walk v w} (h : p.IsTrail)
    (hw : u ∈ p.support) : (p.dropUntil u hw).IsTrail := by
  simp [isTrail_def] at h ⊢
  exact List.nodup_of_sublist (darts_dropUntil_subset _ _) h

end Walk

/-- Defines a path in a digraph: a walk with no repeating vertices. -/
structure Path (G : Digraph V) (u v : V) extends G.Walk u v where
  /-- Every path is also a walk. -/
  is_path : toWalk.IsPath

namespace Path

variable {G} {u v w : V}

/-- Extract the underlying walk of a path. -/
def walk (p : G.Path u v) : G.Walk u v := p.toWalk

instance [Inhabited V] [∀ u v, Inhabited (G.Walk u v)] : Inhabited (G.Path u v) :=
  ⟨{toWalk := default, is_path := by simp [isPath_def]}⟩

@[ext]
theorem ext {p q : G.Path u v} : p.walk = q.walk → p = q := by
  cases p; cases q; simp [walk]

theorem ext_iff {p q : G.Path u v} : p = q ↔ p.walk = q.walk := by
  constructor <;> intro h
  · rw [h]
  · ext; exact h

end Path

/-! ### Reachability and Connectivity -/

/-- Two vertices are *reachable* if there is a walk between them. -/
def Reachable (G : Digraph V) (u v : V) : Prop := Nonempty (G.Walk u v)

/-- Two vertices are *strongly reachable* if they are mutually reachable:
    there are walks in both directions between them. -/
def StronglyReachable (G : Digraph V) (u v : V) : Prop := G.Reachable u v ∧ G.Reachable v u

/-- Two vertices are *weakly reachable* if there is a walk between them in the
    underlying undirected graph. -/
def WeaklyReachable (G : Digraph V) (u v : V) : Prop :=
  ∃ (p : List V), p.length > 0 ∧ u = p.head! ∧ v = p.getLast! ∧
    ∀ i, i < p.length - 1 → G.Adj (p.get! i) (p.get! (i+1)) ∨ G.Adj (p.get! (i+1)) (p.get! i)

/-- A digraph is connected if any two distinct vertices are connected by a walk. -/
def Connected (G : Digraph V) : Prop := ∀ u v, u ≠ v → G.Reachable u v

/-- A digraph is strongly connected if any two distinct vertices are connected by walks
    in both directions. -/
def StronglyConnected (G : Digraph V) : Prop := ∀ u v, u ≠ v → G.StronglyReachable u v

/-- A digraph is weakly connected if any two distinct vertices are connected
    in the underlying undirected graph. -/
def WeaklyConnected (G : Digraph V) : Prop := ∀ u v, u ≠ v → G.WeaklyReachable u v

theorem StronglyConnected.connected {G : Digraph V} (h : G.StronglyConnected) : G.Connected :=
  fun u v huv => (h u v huv).1

theorem StronglyConnected.weaklyConnected {G : Digraph V} (h : G.StronglyConnected) : G.WeaklyConnected := by
  intro u v huv
  obtain ⟨p⟩ := (h u v huv).1
  induction p with
  | nil => contradiction
  | cons h' p' =>
    use [u, v]
    refine ⟨by simp, rfl, rfl, ?_⟩
    intro i hi
    simp at hi
    cases i
    · simp [h']
    · contradiction

end Digraph
