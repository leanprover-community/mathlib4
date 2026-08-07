/-
Copyright (c) 2026 Justin Lai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justin Lai
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!

# Star Graphs

## Main definitions

* `SimpleGraph.starGraph r` is the star graph on V centered at r. Every non-center vertex is
  adjacent to r.

## Main statements

* `SimpleGraph.isTree_starGraph` proves the star graph is a tree.


## Tags

star graph
-/

@[expose] public section

namespace SimpleGraph

variable {V V' : Type*} (G : SimpleGraph V) (G' : SimpleGraph V')

/-- The star graph on `V` centered at `r`: every non-center vertex is adjacent to `r`. -/
def starGraph (r : V) : SimpleGraph V :=
  .fromRel fun v _ ↦ v = r

instance [DecidableEq V] (r : V) : DecidableRel (starGraph r).Adj :=
  inferInstanceAs (DecidableRel fun x y ↦ x ≠ y ∧ (x = r ∨ y = r))

@[simp]
lemma starGraph_adj {r x y : V} : (starGraph r).Adj x y ↔ x ≠ y ∧ (x = r ∨ y = r) := by
  simp [starGraph, fromRel]

@[simp]
lemma isUniversal_starGraph_self {r : V} : (starGraph r).IsUniversal r := by
  intro _ _
  simpa

variable {G} in
theorem starGraph_le_iff {r : V} : starGraph r ≤ G ↔ G.IsUniversal r := by
  refine ⟨fun h u hne ↦ h <| by simpa, fun h a b hadj ↦ ?_⟩
  grind [starGraph_adj, IsUniversal, Adj.symm]

/-- On (starGraph r), r is adjacent to v iff v ≠ r. -/
lemma starGraph_adj_center_iff {r v : V} : (starGraph r).Adj r v ↔ r ≠ v := by simp

lemma starGraph_center_adj {r v : V} (h : r ≠ v) : (starGraph r).Adj r v :=
  starGraph_adj_center_iff.mpr h

lemma starGraph_center_adj' {r v : V} (h : r ≠ v) : (starGraph r).Adj v r :=
  (starGraph_center_adj h).symm

lemma connected_starGraph (r : V) : (starGraph r).Connected :=
  .of_isUniversal isUniversal_starGraph_self

lemma isAcyclic_starGraph (r : V) : (starGraph r).IsAcyclic := by
  refine isAcyclic_iff_forall_adj_isBridge.mpr fun v w hadj ↦ ?_
  rw [starGraph_adj] at hadj
  wlog! h : v = r
  · rw [Sym2.eq_swap]
    exact this r w v ⟨hadj.1.symm, hadj.2.symm⟩ (hadj.2.resolve_left h)
  · subst h
    apply not_reachable_of_neighborSet_right_eq_empty hadj.1
    ext x
    aesop

lemma isTree_starGraph (r : V) : (starGraph r).IsTree :=
  ⟨connected_starGraph r, isAcyclic_starGraph r⟩

/-- Every non-center vertex of a starGraph has degree one. -/
lemma degree_starGraph_of_ne_center [Fintype V] [DecidableEq V] {r v : V} (h : v ≠ r) :
    (starGraph r).degree v = 1 :=
  degree_eq_one_iff_existsUnique_adj.mpr ⟨r, by simp [h], by grind [starGraph_adj]⟩

/-- The center vertex of a starGraph has degree (card V) - 1. -/
lemma degree_starGraph_center [Fintype V] [DecidableEq V] {r : V} :
    (starGraph r).degree r = Fintype.card V - 1 := by
  simp

theorem cliqueFree_starGraph_three (r : V) : starGraph r |>.CliqueFree 3 :=
  isAcyclic_starGraph r |>.cliqueFree_three

variable {G} in
theorem eq_starGraph_of_isUniversal_of_cliqueFree_three {v : V} (hv : G.IsUniversal v)
    (h3 : G.CliqueFree 3) : G = starGraph v := by
  by_contra! hne
  have := hne.lt_of_le' <| starGraph_le_iff.mpr hv
  obtain ⟨⟨a, b⟩, he, he'⟩ := Set.exists_of_ssubset <| edgeSet_strict_mono this
  classical
  refine h3 {v, a, b} <| is3Clique_triple_iff.mpr ⟨hv ?_, hv ?_, he⟩ <;>
    intro rfl <;> simp [he.ne] at he'

theorem IsUniversal.isAcyclic_iff_cliqueFree_three {v : V} (hv : G.IsUniversal v) :
    G.IsAcyclic ↔ G.CliqueFree 3 where
  mp := IsAcyclic.cliqueFree_three
  mpr h3 := eq_starGraph_of_isUniversal_of_cliqueFree_three hv h3 ▸ isAcyclic_starGraph v

end SimpleGraph
