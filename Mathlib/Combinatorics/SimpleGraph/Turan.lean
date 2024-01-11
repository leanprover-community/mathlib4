/-
Copyright (c) 2024 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
# The Turán graph

This file defines the Turán graph and proves some of its basic properties.

## Main declarations

* `G.IsTuranMaximal r`: predicate saying that `G` has the most number of edges for its number `n`
  of vertices while still being `r + 1`-cliquefree.
* `turanGraph n r`: the canonical `r + 1`-cliquefree Turán graph on `n` vertices.

## TODO

* Port the rest of Turán's theorem from https://github.com/leanprover-community/mathlib4/pull/9317
-/


open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- An `r + 1`-cliquefree graph is `r`-Turán-maximal if any other `r + 1`-cliquefree graph on
the same vertex set has the same or fewer number of edges. -/
def IsTuranMaximal (r : ℕ) : Prop :=
  G.CliqueFree (r + 1) ∧ ∀ (H : SimpleGraph V) [DecidableRel H.Adj],
    H.CliqueFree (r + 1) → H.edgeFinset.card ≤ G.edgeFinset.card

/-- The canonical `r + 1`-cliquefree Turán graph on `n` vertices. -/
def turanGraph (n r : ℕ) : SimpleGraph (Fin n) where Adj v w := v % r ≠ w % r

/-- `turanGraph n 0` is complete. Since the only 1-cliquefree graph is the empty graph,
this shows that `0 < r` is needed in the statement of Turán's theorem. -/
theorem turanGraph_zero_eq_top {n : ℕ} : turanGraph n 0 = ⊤ := by
  ext a b
  simp_rw [turanGraph, top_adj, Nat.mod_zero, not_iff_not, Fin.val_inj]

variable {n r : ℕ}

instance : DecidableRel (turanGraph n r).Adj := by dsimp only [turanGraph]; infer_instance

/-- For `n ≤ r`, `turanGraph n r` is complete. -/
theorem turanGraph_eq_top_of_le {n r} (h : n ≤ r) : turanGraph n r = ⊤ := by
  ext a b
  simp_rw [turanGraph, top_adj, Nat.mod_eq_of_lt (a.2.trans_le h),
    Nat.mod_eq_of_lt (b.2.trans_le h), not_iff_not, Fin.val_inj]

variable (hr : 0 < r)

theorem turanGraph_cliqueFree : (turanGraph n r).CliqueFree (r + 1) := by
  rw [cliqueFree_iff]
  by_contra h
  rw [not_isEmpty_iff] at h
  obtain ⟨f, ha⟩ := h
  simp only [turanGraph, top_adj] at ha
  have := @exists_ne_map_eq_of_card_lt_of_maps_to (Fin (r + 1)) (Fin r) univ univ (by simp)
    (fun x ↦ ⟨(f x).1 % r, Nat.mod_lt _ hr⟩) (by simp)
  obtain ⟨x, _, y, _, d, c⟩ := this
  simp only [Fin.mk.injEq] at c
  exact absurd c ((@ha x y).mpr d)

/-- For `n ≤ r` and `0 < r`, `turanGraph n r` is Turán-maximal. -/
theorem isTuranMaximal_turanGraph_of_le (h : n ≤ r) : (turanGraph n r).IsTuranMaximal r := by
  refine' ⟨turanGraph_cliqueFree hr, _⟩
  intro H _ _
  exact card_le_card (edgeFinset_mono ((turanGraph_eq_top_of_le h).symm ▸ le_top (a := H)))

/-- An `r + 1`-cliquefree Turán-maximal graph is _not_ `r`-cliquefree
if it can accommodate such a clique. -/
theorem not_cliqueFree_of_isTuranMaximal (hn : r ≤ Fintype.card V) (hx : IsTuranMaximal G r) :
    ¬G.CliqueFree r := by
  by_contra cf
  obtain ⟨K, ⟨_, cK⟩⟩ := exists_smaller_set (univ : Finset V) r hn
  have := (G.isNClique_iff).not.mp (cf K)
  simp_rw [cK, and_true, IsClique, Set.Pairwise, not_forall] at this
  obtain ⟨a, _, b, _, ne, na⟩ := this
  have nhx : ¬G.IsTuranMaximal r := by
    simp_rw [IsTuranMaximal, hx.1, true_and]; push_neg
    use G.addEdge a b, inferInstance, cf.addEdge a b
    simp_rw [G.card_edgeFinset_addEdge na ne, Nat.lt.base]
  contradiction

end SimpleGraph
