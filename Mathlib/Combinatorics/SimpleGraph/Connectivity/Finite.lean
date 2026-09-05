/-
Copyright (c) 2021 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Nat
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
public import Mathlib.Data.Set.Card

/-!
# Connectivity in a finite graph

This file provides efficient decidability instances for reachability and (pre)connectedness of
finite graphs through a breadth-first search (BFS) algorithm.
-/

public section

assert_not_exists Field

open Finset Function

universe u v w

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

theorem ConnectedComponent.card_le_card_of_le [Finite V] {G G' : SimpleGraph V} (h : G ≤ G') :
    Nat.card G'.ConnectedComponent ≤ Nat.card G.ConnectedComponent :=
  Nat.card_le_card_of_surjective _ <| ConnectedComponent.surjective_map_ofLE h

/-!
### Deciding reachability by breadth-first search

This section provides efficient decidability instances for reachability and (pre)connectedness of
finite graphs through a breadth-first search (BFS) algorithm.

The algorithm is as follows: we maintain a finset of visited vertices which we grow with all its
neighbors at each round of breadth-first search at, stopping as soon as a round adds no new vertex:
a search costs `O((diam G + 1) * (card V) ^ 2)` adjacency tests.

Vertices `u` and `v` are then reachable if `v` lies in the BFS-constructed finset of vertices
reachable from `u`, and a graph is (pre)connected iff it's non-empty and (/empty or) every vertex is
lies in the reachability finset of an arbitrarily-chosen vertex.
-/

section BFS
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj] {m n : ℕ} {s t : Finset V} {u v w : V}

variable (G s) in
/-- One round of breadth-first search: `G.bfsStep s` consists of the vertices of `s` together with
their neighbours. -/
def bfsStep : Finset V := {w | w ∈ s ∨ ∃ v ∈ s, G.Adj v w}

@[simp, grind =]
lemma mem_bfsStep : w ∈ G.bfsStep s ↔ w ∈ s ∨ ∃ v ∈ s, G.Adj v w := by simp [bfsStep]

lemma subset_bfsStep : s ⊆ G.bfsStep s := fun _ hw ↦ G.mem_bfsStep.2 <| .inl hw

@[gcongr] lemma bfsStep_mono (hst : s ⊆ t) : G.bfsStep s ⊆ G.bfsStep t := by grind

@[gcongr]
lemma iterate_bfsStep_mono (hst : s ⊆ t) : G.bfsStep^[n] s ⊆ G.bfsStep^[n] t := by
  induction n generalizing s t with
  | zero => exact hst
  | succ n ih => simpa only [Function.iterate_succ_apply] using ih (G.bfsStep_mono hst)

lemma subset_iterate_bfsStep : s ⊆ G.bfsStep^[n] s := by
  induction n with
  | zero => exact subset_rfl
  | succ n ih => grw [Function.iterate_succ_apply', ih, ← G.subset_bfsStep]

lemma iterate_bfsStep_subset_of_le (hmn : m ≤ n) : G.bfsStep^[m] s ⊆ G.bfsStep^[n] s := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [Function.iterate_add_apply]
  exact G.iterate_bfsStep_mono G.subset_iterate_bfsStep

lemma mem_iterate_bfsStep_of_walk (p : G.Walk u v) : v ∈ G.bfsStep^[p.length] {u} := by
  induction p with
  | nil => simp
  | cons h p ih =>
    rw [Walk.length_cons, Function.iterate_succ_apply]
    exact G.iterate_bfsStep_mono (by simp [h]) ih

lemma reachable_of_mem_iterate_bfsStep (hv : v ∈ G.bfsStep^[n] {u}) : G.Reachable u v := by
  induction n generalizing v with
  | zero =>
    rw [Function.iterate_zero_apply, Finset.mem_singleton] at hv
    exact hv ▸ Reachable.refl _
  | succ n ih =>
    rw [Function.iterate_succ_apply', mem_bfsStep] at hv
    obtain hv | ⟨w, hw, hwv⟩ := hv
    · exact ih hv
    · exact (ih hw).trans hwv.reachable

/-- Iterate `G.bfsStep` at most `n` times, stopping as soon as no new vertex shows up. -/
def bfsIterate : ℕ → Finset V → Finset V
  | 0, s => s
  | n + 1, s => if (G.bfsStep s).card ≤ s.card then s else bfsIterate n (G.bfsStep s)

lemma bfsIterate_eq_iterate_bfsStep (n : ℕ) (s : Finset V) :
    G.bfsIterate n s = G.bfsStep^[n] s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    rw [bfsIterate]
    split_ifs with h
    · have hs : G.bfsStep s = s := (Finset.eq_of_subset_of_card_le G.subset_bfsStep h).symm
      exact (Function.iterate_fixed hs _).symm
    · rw [ih, ← Function.iterate_succ_apply]

/-- The finset of vertices reachable from `u`, computed by breadth-first search. -/
def reachableFinset (u : V) : Finset V := G.bfsIterate (Fintype.card V) {u}

@[simp]
lemma mem_reachableFinset : v ∈ G.reachableFinset u ↔ G.Reachable u v := by
  rw [reachableFinset, bfsIterate_eq_iterate_bfsStep]
  refine ⟨G.reachable_of_mem_iterate_bfsStep, fun h ↦ h.elim_path fun p ↦ ?_⟩
  exact G.iterate_bfsStep_subset_of_le p.2.length_lt.le (G.mem_iterate_bfsStep_of_walk p.1)

/-- Decides reachability of vertices `u` and `v` by performing a breadth-first search from `u`. -/
instance decidableReachable : DecidableRel G.Reachable :=
  fun _ _ ↦ decidable_of_iff _ G.mem_reachableFinset

lemma preconnected_iff_forall_mem_reachableFinset (u : V) :
    G.Preconnected ↔ ∀ v, v ∈ G.reachableFinset u := by
  simp only [mem_reachableFinset]
  exact ⟨fun h v ↦ h u v, fun h x y ↦ (h x).symm.trans (h y)⟩

/-- Decides preconnectedness of `G` by checking whether the vertex set is empty and, if not,
by performing a breadth-first search from an arbitrarily chosen vertex. -/
instance decidablePreconnected : Decidable G.Preconnected :=
  if h : Fintype.card V = 0 then
    isTrue (by rw [Fintype.card_eq_zero_iff] at h; exact .of_subsingleton)
  else
    (truncOfCardPos <| by lia).lift
      (fun u ↦ decidable_of_iff _ (G.preconnected_iff_forall_mem_reachableFinset u).symm)
      fun _ _ ↦ Subsingleton.elim _ _

lemma connected_iff_forall_mem_reachableFinset (u : V) :
    G.Connected ↔ ∀ v, v ∈ G.reachableFinset u := by
  rw [connected_iff, G.preconnected_iff_forall_mem_reachableFinset u, and_iff_left ⟨u⟩]

/-- Decides preconnectedness of `G` by checking whether the vertex set is empty and, if not,
by performing a breadth-first search from an arbitrarily chosen vertex. -/
instance decidableConnected : Decidable G.Connected :=
  if h : Fintype.card V = 0 then
    isFalse fun hG ↦ (Fintype.card_eq_zero_iff.1 h).false hG.nonempty.some
  else
    (truncOfCardPos <| by lia).lift
      (fun u ↦ decidable_of_iff _ (G.connected_iff_forall_mem_reachableFinset u).symm)
      fun _ _ ↦ Subsingleton.elim ..

instance : Fintype G.ConnectedComponent :=
  fast_instance% @Quotient.fintype _ _ G.reachableSetoid (inferInstance : DecidableRel G.Reachable)

instance instDecidableMemSupp (c : G.ConnectedComponent) (v : V) : Decidable (v ∈ c.supp) :=
  c.recOn (fun w ↦ decidable_of_iff (G.Reachable v w) <| by simp)
    (fun _ _ _ _ ↦ Subsingleton.elim _ _)

end BFS

section Fintype

variable [DecidableEq V] [Fintype V] [DecidableRel G.Adj]

theorem reachable_iff_exists_finsetWalkLength_nonempty (u v : V) :
    G.Reachable u v ↔ ∃ n : Fin (Fintype.card V), (G.finsetWalkLength n u v).Nonempty := by
  constructor
  · intro r
    refine r.elim_path fun p => ?_
    refine ⟨⟨_, p.isPath.length_lt⟩, p, ?_⟩
    simp [mem_finsetWalkLength_iff]
  · rintro ⟨_, p, _⟩
    exact ⟨p⟩

set_option backward.isDefEq.respectTransparency.types false in
lemma disjiUnion_supp_toFinset_eq_supp_toFinset {G' : SimpleGraph V} (h : G ≤ G')
    (c' : ConnectedComponent G') [Fintype c'.supp]
    [DecidablePred fun c : G.ConnectedComponent ↦ c.supp ⊆ c'.supp] :
    .disjiUnion {c : ConnectedComponent G | c.supp ⊆ c'.supp} (fun c ↦ c.supp.toFinset)
      (fun x _ y _ hxy ↦ by simpa using pairwise_disjoint_supp_connectedComponent _ hxy) =
      c'.supp.toFinset :=
  Finset.coe_injective <| by simpa using ConnectedComponent.biUnion_supp_eq_supp h _

end Fintype

/-- The odd components are the connected components of odd cardinality. This definition excludes
infinite components. -/
abbrev oddComponents : Set G.ConnectedComponent := {c : G.ConnectedComponent | Odd c.supp.ncard}

set_option backward.isDefEq.respectTransparency.types false in
lemma ConnectedComponent.odd_oddComponents_ncard_subset_supp [Finite V] {G'}
    (h : G ≤ G') (c' : ConnectedComponent G') :
    Odd {c ∈ G.oddComponents | c.supp ⊆ c'.supp}.ncard ↔ Odd c'.supp.ncard := by
  simp_rw [← Nat.card_coe_set_eq]
  classical
  cases nonempty_fintype V
  rw [Nat.card_eq_card_toFinset c'.supp, ← disjiUnion_supp_toFinset_eq_supp_toFinset h]
  simp only [Finset.card_disjiUnion, Set.toFinset_card, Fintype.card_ofFinset]
  rw [Finset.odd_sum_iff_odd_card_odd, Nat.card_eq_fintype_card, Fintype.card_ofFinset]
  congr! 2
  ext c
  simp_rw [Set.toFinset_ofPred, mem_filter, ← Set.ncard_coe_finset, coe_filter,
    mem_supp_iff, mem_univ, true_and, supp, and_comm]

lemma odd_ncard_oddComponents [Finite V] : Odd G.oddComponents.ncard ↔ Odd (Nat.card V) := by
  classical
  cases nonempty_fintype V
  rw [Nat.card_eq_fintype_card]
  simp only [← (set_fintype_card_eq_univ_iff _).mpr G.iUnion_connectedComponentSupp,
    ← Set.toFinset_card, Set.toFinset_iUnion ConnectedComponent.supp]
  rw [Finset.card_biUnion
    (fun x _ y _ hxy ↦ Set.disjoint_toFinset.mpr (pairwise_disjoint_supp_connectedComponent _ hxy))]
  simp_rw [← Set.ncard_eq_toFinset_card', ← Finset.coe_filter_univ, Set.ncard_coe_finset]
  exact (Finset.odd_sum_iff_odd_card_odd (fun x : G.ConnectedComponent ↦ x.supp.ncard)).symm

lemma ncard_oddComponents_mono [Finite V] {G' : SimpleGraph V} (h : G ≤ G') :
     G'.oddComponents.ncard ≤ G.oddComponents.ncard := by
  have aux (c : G'.ConnectedComponent) (hc : Odd c.supp.ncard) :
      {c' : G.ConnectedComponent | Odd c'.supp.ncard ∧ c'.supp ⊆ c.supp}.Nonempty := by
    refine Set.nonempty_of_ncard_ne_zero fun h' ↦ Nat.not_odd_zero ?_
    rw [← h']
    exact (c.odd_oddComponents_ncard_subset_supp h).2 hc
  let f : G'.oddComponents → G.oddComponents :=
    fun ⟨c, hc⟩ ↦ ⟨(aux c hc).choose, (aux c hc).choose_spec.1⟩
  refine Nat.card_le_card_of_injective f fun c c' fcc' ↦ ?_
  simp only [Subtype.mk.injEq, f] at fcc'
  exact Subtype.val_injective (ConnectedComponent.eq_of_common_vertex
    ((fcc' ▸ (aux c.1 c.2).choose_spec.2) (ConnectedComponent.nonempty_supp _).some_mem)
      ((aux c'.1 c'.2).choose_spec.2 (ConnectedComponent.nonempty_supp _).some_mem))

end SimpleGraph
