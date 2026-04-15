/-
Copyright (c) 2026 Justin Lai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justin Lai
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Metric

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

/-- If r ≠ v, then v is adjacent to r. -/
lemma starGraph_center_adj {r v : V} (h : r ≠ v) : (starGraph r).Adj r v :=
  starGraph_adj.mpr ⟨h, Or.inl rfl⟩

lemma starGraph_center_adj' {r v : V} (h : r ≠ v) : (starGraph r).Adj v r :=
  (starGraph_center_adj h).symm

lemma connected_starGraph (r : V) : (starGraph r).Connected := by
  have (v : V) : (starGraph r).Reachable r v := by
    by_cases! h : r = v
    · exact h ▸ Reachable.rfl
    · exact (starGraph_center_adj h).reachable
  exact connected_iff _ |>.mpr ⟨fun u v ↦ (this u).symm.trans (this v), ⟨r⟩⟩

lemma isAcyclic_starGraph (r : V) : (starGraph r).IsAcyclic := by
  refine isAcyclic_iff_forall_adj_isBridge.mpr fun v w hadj ↦ isBridge_iff.mpr ⟨hadj, ?_⟩
  rw [starGraph_adj] at hadj
  wlog! h : v = r
  · have hw : w = r := hadj.2.resolve_left h
    replace hadj : w ≠ v ∧ (w = r ∨ v = r) := ⟨hadj.1.symm, hadj.2.symm⟩
    rw [reachable_comm, Sym2.eq_swap]
    exact this r w v hadj hw
  · subst h
    apply not_reachable_of_neighborSet_right_eq_empty hadj.1
    ext x; aesop

/-- A star graph is a tree. -/
lemma isTree_starGraph (r : V) : (starGraph r).IsTree := by
  refine ⟨connected_starGraph r, isAcyclic_starGraph r⟩

/-- Every non-center vertex of a starGraph has degree one. -/
lemma degree_starGraph_of_ne_center [Fintype V] [DecidableEq V] {r v : V} (h : v ≠ r) :
    (starGraph r).degree v = 1 :=
  degree_eq_one_iff_existsUnique_adj.mpr ⟨r, by simp [h], by grind [starGraph_adj]⟩

/-- The center vertex of a starGraph has degree (card V) - 1. -/
lemma degree_starGraph_center [Fintype V] [DecidableEq V] {r : V} :
    (starGraph r).degree r = Fintype.card V - 1 := by
  rw [degree, neighborFinset_eq_filter (starGraph r)]
  simp only [starGraph_adj, ne_eq, true_or, and_true]
  have : ({w | ¬r = w} : Finset V) = Finset.univ.erase r := by
    ext v; simp [eq_comm]
  rw [this, Finset.card_erase_of_mem (Finset.mem_univ r), Finset.card_univ]

end SimpleGraph
