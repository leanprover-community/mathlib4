/-
Copyright (c) 2026 Kyle Miller, Laurance Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurance Lau
-/
module

public import Mathlib.Combinatorics.Digraph.Walk

/-!
# Directed acyclic graphs

This module introduces *acyclic digraphs*, also known as *directed acyclic graphs (DAGs)*.

## Main definitions

* `Digraph.IsAcyclic` is a predicate for a digraph having no cyclic walks.
This definition is similar to that for `SimpleGraph`.

## Tags

acyclic digraphs, directed acyclic graphs
-/

@[expose] public section

namespace Digraph

/-- A digraph is *acyclic* if it has no cycles. -/
def IsAcyclic {V : Type*} (G : Digraph V) : Prop := ∀ ⦃v : V⦄ (c : G.Walk v v), ¬c.IsCycle

namespace IsAcyclic

variable {V : Type*} {G : Digraph V} {u v : V}

lemma irrefl (h : G.IsAcyclic) : ¬G.Adj u u := by
  intro h'
  have := h h'.toWalk
  contrapose! this
  exact ⟨by tauto, by simp⟩

lemma ne_of_adj (h : G.IsAcyclic) (hadj : G.Adj u v) : u ≠ v := by
  grind [h.irrefl]

lemma not_adj_symm (h : G.IsAcyclic) (hadj : G.Adj u v) : ¬G.Adj v u := by
  intro h'
  have := h (hadj.toWalk.cons h')
  contrapose! this
  exact ⟨by tauto, by simpa [Walk.support] using h.ne_of_adj hadj⟩

end IsAcyclic

end Digraph
