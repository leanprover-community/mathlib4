/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller

! This file was ported from Lean 3 source module combinatorics.simple_graph.acyclic
! leanprover-community/mathlib commit b07688016d62f81d14508ff339ea3415558d6353
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Combinatorics.SimpleGraph.Connectivity

/-!

# Acyclic graphs and trees

This module introduces *acyclic graphs* (a.k.a. *forests*) and *trees*.

## Main definitions

* `simple_graph.is_acyclic` is a predicate for a graph having no cyclic walks
* `simple_graph.is_tree` is a predicate for a graph being a tree (a connected acyclic graph)

## Main statements

* `simple_graph.is_acyclic_iff_path_unique` characterizes acyclicity in terms of uniqueness of
  paths between pairs of vertices.
* `simple_graph.is_acyclic_iff_forall_edge_is_bridge` characterizes acyclicity in terms of every
  edge being a bridge edge.
* `simple_graph.is_tree_iff_exists_unique_path` characterizes trees in terms of existence and
  uniqueness of paths between pairs of vertices from a nonempty vertex type.

## References

The structure of the proofs for `simple_graph.is_acyclic` and `simple_graph.is_tree`, including
supporting lemmas about `simple_graph.is_bridge`, generally follows the high-level description
for these theorems for multigraphs from [Chou1994].

## Tags

acyclic graphs, trees
-/


universe u v

namespace SimpleGraph

variable {V : Type u} (G : SimpleGraph V)

/-- A graph is *acyclic* (or a *forest*) if it has no cycles. -/
def IsAcyclic : Prop :=
  ∀ (v : V) (c : G.Walk v v), ¬c.IsCycle
#align simple_graph.is_acyclic SimpleGraph.IsAcyclic

/-- A *tree* is a connected acyclic graph. -/
-- porting note: `protect_proj` not (yet) implemented. -/
-- @[mk_iff, protect_proj]
@[mk_iff]
structure IsTree : Prop where
  is_connected : G.Connected
  IsAcyclic : G.IsAcyclic
#align simple_graph.is_tree SimpleGraph.IsTree

variable {G}

theorem isAcyclic_iff_forall_adj_isBridge :
    G.IsAcyclic ↔ ∀ ⦃v w : V⦄, G.Adj v w → G.IsBridge ⟦(v, w)⟧ := by
  simp_rw [isBridge_iff_adj_and_forall_cycle_not_mem]
  constructor
  · intro ha v w hvw
    apply And.intro hvw
    intro u p hp
    exact absurd hp (ha _ p)
  · rintro hb v (_ | @⟨_, _, _, ha, p⟩) hp
    · exact hp.not_of_nil
    · specialize hb ha
      apply hb.2 _ hp
      rw [Walk.edges_cons]
      apply List.mem_cons_self
#align simple_graph.is_acyclic_iff_forall_adj_is_bridge SimpleGraph.isAcyclic_iff_forall_adj_isBridge

theorem isAcyclic_iff_forall_edge_isBridge :
    G.IsAcyclic ↔ ∀ ⦃e⦄, e ∈ (edgeSetEmbedding V G) → G.IsBridge e := by
  simp [isAcyclic_iff_forall_adj_isBridge, Sym2.forall]
#align simple_graph.is_acyclic_iff_forall_edge_is_bridge SimpleGraph.isAcyclic_iff_forall_edge_isBridge

theorem IsAcyclic.path_unique {G : SimpleGraph V} (h : G.IsAcyclic) {v w : V} (p q : G.Path v w) :
    p = q := by
  obtain ⟨p, hp⟩ := p
  obtain ⟨q, hq⟩ := q
  simp only
  induction' p with u pu pv pw ph p ih
  · rw [Walk.isPath_iff_eq_nil] at hq
    simp only [hq.symm]
  · rw [isAcyclic_iff_forall_adj_isBridge] at h
    specialize h ph
    rw [isBridge_iff_adj_and_forall_walk_mem_edges] at h
    replace h := h.2 (q.append p.reverse)
    simp only [Walk.edges_append, Walk.edges_reverse, List.mem_append, List.mem_reverse'] at h
    cases' h with h
    · cases q
      · simp [Walk.isPath_def] at hp
      · rw [Walk.cons_isPath_iff] at hp hq
        simp only [Walk.edges_cons, List.mem_cons, Sym2.eq_iff] at h
        obtain (⟨h, rfl⟩ | ⟨rfl, rfl⟩) | h := h
        · rw [ih hp.1 _ hq.1]
        · simpa using hq
        · exact absurd (Walk.fst_mem_support_of_mem_edges _ h) hq.2
    · rw [Walk.cons_isPath_iff] at hp
      exact absurd (Walk.fst_mem_support_of_mem_edges _ h) hp.2
#align simple_graph.is_acyclic.path_unique SimpleGraph.IsAcyclic.path_unique

theorem isAcyclic_of_path_unique (h : ∀ (v w : V) (p q : G.Path v w), p = q) : G.IsAcyclic := by
  intro v c hc
  simp only [Walk.isCycle_def, Ne.def] at hc
  cases c
  · exact absurd rfl hc.2.1
  · simp only [Walk.cons_isTrail_iff, not_false_iff, Walk.support_cons, List.tail_cons,
      true_and_iff] at hc
    specialize h _ _ ⟨c_p, by simp only [Walk.is_path_def, hc.2]⟩ (Path.singleton (G.symm c_h))
    simp only [Path.singleton] at h
    simpa [-Quotient.eq', Sym2.eq_swap, h] using hc
#align simple_graph.is_acyclic_of_path_unique SimpleGraph.isAcyclic_of_path_unique

theorem isAcyclic_iff_path_unique : G.IsAcyclic ↔ ∀ ⦃v w : V⦄ (p q : G.Path v w), p = q :=
  ⟨IsAcyclic.path_unique, isAcyclic_of_path_unique⟩
#align simple_graph.is_acyclic_iff_path_unique SimpleGraph.isAcyclic_iff_path_unique

theorem isTree_iff_existsUnique_path :
    G.IsTree ↔ Nonempty V ∧ ∀ v w : V, ∃! p : G.Walk v w, p.IsPath := by
  classical
    rw [IsTree_iff, isAcyclic_iff_path_unique]
    constructor
    · rintro ⟨hc, hu⟩
      refine' ⟨hc.nonempty, _⟩
      intro v w
      let q := (hc v w).some.toPath
      use q
      simp only [true_and_iff, Path.isPath]
      intro p hp
      specialize hu ⟨p, hp⟩ q
      exact Subtype.ext_iff.mp hu
    · rintro ⟨hV, h⟩
      refine' ⟨Connected.mk _, _⟩
      · intro v w
        obtain ⟨p, _⟩ := h v w
        exact p.reachable
      · rintro v w ⟨p, hp⟩ ⟨q, hq⟩
        simp only [ExistsUnique.unique (h v w) hp hq]
#align simple_graph.is_tree_iff_exists_unique_path SimpleGraph.isTree_iff_existsUnique_path

end SimpleGraph
