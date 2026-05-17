/-
Copyright (c) 2021 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Peter Nelson
-/
module

public import Mathlib.Combinatorics.SimpleGraph.GraphLike
public import Mathlib.Combinatorics.GraphLike.Walks.Simple

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

open SimpleGraph SymmGraphLike

variable {V : Type*} {G : SimpleGraph V} {u v w : V}

/-- The one-edge walk associated to a pair of adjacent vertices. -/
@[expose, match_pattern, reducible]
def SimpleGraph.Adj.toWalk {u v : V} (h : Adj G u v) : GraphLike.Walk G u v :=
  GraphLike.Walk.cons h.toStep GraphLike.Walk.nil

namespace GraphLike.Walk

theorem adj_of_mem_edges {u v x y : V} (p : Walk G u v) (h : s(x, y) ∈ p.edges) : G.Adj x y :=
  p.edges_subset_edgeSet h

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

lemma nil_of_subsingleton [Subsingleton V] (p : Walk G v w) : p.Nil :=
  match p with
  | nil => Nil.nil
  | cons s w => (Unique.eq_default G ▸ s).adj |>.elim

theorem mem_support_iff_exists_mem_edges_of_not_nil {u v w : V} {p : Walk G u v} (hnil : ¬p.Nil) :
    w ∈ p.support ↔ ∃ e ∈ p.edges, w ∈ e := by
  induction p with
  | nil => simp at hnil
  | cons h p ih => cases p <;> aesop

theorem darts_getElem_eq_fst_snd {u v} {p : Walk G u v} {i : ℕ} (hi : i < p.darts.length) :
    p.darts[i] = (p.support[i]'(by grind), p.support[i + 1]'(by grind)) := by
  match i, p with
  | 0, .cons s_2 p_2 => simp
  | n_1 + 1, .cons s_2 p_2 =>
    simp only [darts_cons, val_step_eq, List.getElem_cons_succ, support_cons]
    exact p_2.darts_getElem_eq_fst_snd _

end Walk

end GraphLike
