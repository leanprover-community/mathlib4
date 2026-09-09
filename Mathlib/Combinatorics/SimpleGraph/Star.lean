/-
Copyright (c) 2026 Justin Lai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justin Lai
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.CompleteMultipartite

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

variable {V : Type*} (r : V)

/-- The star graph on `V` centered at `r`: every non-center vertex is adjacent to `r`. -/
def starGraph (r : V) : SimpleGraph V :=
  .fromRel fun v _ ↦ v = r

instance [DecidableEq V] (r : V) : DecidableRel (starGraph r).Adj :=
  inferInstanceAs (DecidableRel fun x y ↦ x ≠ y ∧ (x = r ∨ y = r))

@[simp, grind =]
lemma starGraph_adj {r x y : V} : (starGraph r).Adj x y ↔ x ≠ y ∧ (x = r ∨ y = r) := by
  simp [starGraph, fromRel]

@[simp]
lemma isUniversal_starGraph_self {r : V} : (starGraph r).IsUniversal r := by
  intro _ _
  simpa

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

/-- Bicoloring of a star graph -/
def Coloring.starGraphBool [DecidableEq V] : (starGraph r).Coloring Bool where
  toFun v := v = r
  map_rel' := by grind [top_adj]

theorem IsBipartite.starGraph : (starGraph r).IsBipartite := by
  classical
  simpa using Coloring.starGraphBool r |>.colorable

theorem IsBipartiteWith.starGraph : (starGraph r).IsBipartiteWith {r} {r}ᶜ := by
  grind [IsBipartiteWith]

theorem IsCompleteBetween.starGraph : (starGraph r).IsCompleteBetween {r} {r}ᶜ := by
  grind [IsCompleteBetween]

theorem IsCompleteMultipartite.starGraph : (starGraph r).IsCompleteMultipartite := by
  grind [IsCompleteMultipartite, isTrans_def]

/-- Every non-center vertex of a starGraph has degree one. -/
lemma degree_starGraph_of_ne_center [Fintype V] [DecidableEq V] {r v : V} (h : v ≠ r) :
    (starGraph r).degree v = 1 :=
  degree_eq_one_iff_existsUnique_adj.mpr ⟨r, by simp [h], by grind⟩

/-- The center vertex of a starGraph has degree (card V) - 1. -/
lemma degree_starGraph_center [Fintype V] [DecidableEq V] {r : V} :
    (starGraph r).degree r = Fintype.card V - 1 := by
  simp

theorem starGraph_inl_unitMk : starGraph (.inl ()) = completeBipartiteGraph Unit V := by
  grind

theorem starGraph_inr_unitMk : starGraph (.inr ()) = completeBipartiteGraph V Unit := by
  grind

end SimpleGraph
