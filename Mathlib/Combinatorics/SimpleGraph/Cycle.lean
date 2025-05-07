/-
Copyright (c) 2025 Yunge Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunge Yu
-/
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Combinatorics.SimpleGraph.Trails

/-!

# Cycle Graphs

This module introduces *cycle graphs*.

## Main definitions

* `SimpleGraph.IsCycle` is a predicate for a graph being a cycle graph

## Tags

cycle graphs
-/

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

variable [Fintype V] [DecidableRel G.Adj]

/-- A graph is a *cycle* if it is connected, and every vertex has degree 2. -/
def IsCycle : Prop := G.Connected ∧ (∀ (v : V), G.degree v = 2)

namespace IsCycle

lemma Connected (c : G.IsCycle) : G.Connected := c.1

lemma all_vertices_degree_two (c : G.IsCycle) : ∀ (v : V), G.degree v = 2 := c.2

lemma vertex_card_eq_edge_card (c : G.IsCycle) : Fintype.card V = Fintype.card G.edgeSet := by
  have h_v_card : ∑ (v : V), G.degree v = 2*(Fintype.card V) := by
    have hd : ∀ v ∈ (Finset.univ : Finset V), G.degree v ≤ 2 := by simp [c.2]
    simp only [← Finset.card_univ, Finset.card_eq_sum_ones, Finset.mul_sum, mul_one,
      Finset.sum_eq_sum_iff_of_le hd, Finset.mem_univ, forall_const, c.2]
  simp_all [G.sum_degrees_eq_twice_card_edges]

lemma three_le_card (c : G.IsCycle) : 3 ≤ Fintype.card V := by
  obtain ⟨hc, hd⟩ := c
  rw [connected_iff] at hc
  obtain ⟨_, ⟨v⟩⟩ := hc
  have h_n_card := Finset.card_lt_univ_of_not_mem (G.not_mem_neighborFinset_self v)
  rw [G.card_neighborFinset_eq_degree, hd] at h_n_card
  simp [Nat.add_one_le_iff, h_n_card]

variable {v w : V}

lemma IsCycles (c : G.IsCycle) : G.IsCycles := by
  intro v hv
  have h_n_card : Fintype.card (G.neighborSet v) = 2 := by
    rw [G.card_neighborSet_eq_degree, c.2]
  simp only [Fintype.card_ofFinset, mem_neighborSet] at h_n_card
  simp [Set.ncard_eq_toFinset_card', h_n_card]

lemma exists_adj (c : G.IsCycle) : ∃ (w : V), G.Adj v w := by
  have hd : G.degree v > 0 := by simp [c.2]
  exact (G.degree_pos_iff_exists_adj v).mp hd

lemma neighborSet_nonempty (c : G.IsCycle) : (G.neighborSet v).Nonempty := c.exists_adj

lemma no_bridges (c : G.IsCycle) (hadj : G.Adj v w) : ¬G.IsBridge s(v, w) := by
  simp only [isBridge_iff, hadj, true_and, not_not]
  exact IsCycles.reachable_deleteEdges hadj c.IsCycles

lemma notTree (c : G.IsCycle) : ¬G.IsTree := by
  simp [G.isTree_iff_connected_and_card, c.vertex_card_eq_edge_card]

lemma notAcyclic (c : G.IsCycle) : ¬G.IsAcyclic := by
  have h_not_tree := c.notTree
  simp only [G.isTree_iff, c.1, true_and] at h_not_tree
  exact h_not_tree

lemma isCyclic (c : G.IsCycle) : ∃ (v : V) (p : G.Walk v v), p.IsCycle := by
  have h_not_acyclic := c.notAcyclic
  simp_all [IsAcyclic]

lemma all_vertices_form_a_cycle (c : G.IsCycle) : ∃ (p : G.Walk v v), p.IsCycle := by
  have hv : v ∈ G.connectedComponentMk v := ConnectedComponent.connectedComponentMk_mem
  obtain ⟨p, hpc, _⟩ := IsCycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
    c.IsCycles hv c.neighborSet_nonempty
  use p

lemma cycle_walk_contains_all_vertices {p : G.Walk v v} (c : G.IsCycle) (hpc : p.IsCycle) :
    ∀ (w : V), w ∈ p.support := by
  intro w
  have hvw_reachable : G.Reachable v w := c.1 v w
  have hpv : p.toSubgraph.verts = (G.connectedComponentMk v).supp := by
    have : ∀ v ∈ p.toSubgraph.verts, ∀ (w : V), G.Adj v w → p.toSubgraph.Adj v w := by
      intro v hv w hvw
      refine (Subgraph.adj_iff_of_neighborSet_equiv ?_ (Set.toFinite _)).mpr hvw
      refine @Classical.ofNonempty _ ?_
      rw [← Cardinal.eq, ← Set.cast_ncard (Set.toFinite _), ← Set.cast_ncard (Set.toFinite _),
        c.IsCycles G c.exists_adj,
        hpc.ncard_neighborSet_toSubgraph_eq_two (p.mem_verts_toSubgraph.mp hv)]
    obtain ⟨cc, hcc⟩ := p.toSubgraph_connected.exists_verts_eq_connectedComponentSupp this
    rw [hcc]
    have : v ∈ cc.supp := by simp [← hcc]
    simp_all
  rw [← Walk.mem_verts_toSubgraph, hpv]
  have hvw : G.connectedComponentMk v = G.connectedComponentMk w :=
    ConnectedComponent.sound hvw_reachable
  simp [hvw]

lemma cycle_walk_tail_contains_all_vertices {p : G.Walk v v} (c : G.IsCycle) (hpc : p.IsCycle) :
    ∀ (w : V), w ∈ p.support.tail := by
  have : ∀ (w : V), w ∈ p.support ↔ w ∈ p.support.tail := by
    intro w
    constructor
    · intro
      have : p.support ≠ [] := p.support_ne_nil
      by_cases h : w = p.support.head this
      · simp only [Walk.head_support] at h
        rw [h]
        exact Walk.end_mem_tail_support hpc.not_nil
      · cases hs : p.support with
        | nil => contradiction
        | cons head tail => simp_all
    · exact List.mem_of_mem_tail
  simp only [← this]
  exact c.cycle_walk_contains_all_vertices G hpc

variable [DecidableEq V]

lemma cycle_walk_contains_all_edges {p : G.Walk v v} (c : G.IsCycle) (h : p.IsCycle) :
    ∀ e ∈ G.edgeSet, e ∈ p.edges := by
  have h_stl_tsl : p.support.tail.length = p.tail.support.length := by
    simp [p.support_tail h.not_nil]
  have h_support_length : p.support.tail.length = Fintype.card V := by
    rw [← List.toFinset_card_of_nodup h.support_nodup]
    have : ∀ (v : V), v ∈ p.support.tail.toFinset := by
      simp [c.cycle_walk_tail_contains_all_vertices G h]
    rw [← Finset.eq_univ_iff_forall] at this
    simp [this]
  rw [c.vertex_card_eq_edge_card, h_stl_tsl, p.tail.length_support, p.length_tail_add_one h.not_nil,
    ← p.length_edges, ← List.toFinset_card_of_nodup h.edges_nodup, ← edgeFinset_card]
    at h_support_length
  have : ∀ e ∈ G.edgeSet, e ∈ p.edgeSet := by
    have : p.edgeSet = G.edgeSet := by
      have : p.edges.toFinset ⊆ G.edgeFinset := by
        simp only [Set.subset_toFinset, List.coe_toFinset]
        apply Walk.edges_subset_edgeSet
      have : p.edges.toFinset = G.edgeFinset :=
        Finset.eq_of_subset_of_card_le this h_support_length.ge
      calc
        p.edgeSet = ↑p.edges.toFinset := (Walk.coe_edges_toFinset _).symm
        _ = ↑G.edgeFinset := by rw [this]
        _ = G.edgeSet := coe_edgeFinset _
    simp [this]
  simp_all

theorem IsEulerian (c : G.IsCycle) : ∃ (v : V) (p : G.Walk v v), p.IsEulerian := by
  simp only [Walk.isEulerian_iff]
  obtain ⟨v, p, hpc⟩ := c.isCyclic
  use v
  use p
  simp only [hpc.isCircuit.isTrail, true_and]
  exact c.cycle_walk_contains_all_edges G hpc

lemma IsHamiltonian (c : G.IsCycle) : G.IsHamiltonian := by
  unfold SimpleGraph.IsHamiltonian
  intro
  obtain ⟨v, p, hcyc⟩ := c.isCyclic
  use v
  use p
  simp only [Walk.isHamiltonianCycle_iff_isCycle_and_support_count_tail_eq_one, hcyc, true_and]
  intro v
  have : v ∈ p.support.tail := by apply c.cycle_walk_tail_contains_all_vertices G hcyc
  apply List.count_eq_one_of_mem hcyc.support_nodup this

end IsCycle

end SimpleGraph
