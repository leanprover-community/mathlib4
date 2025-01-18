/-
Copyright (c) 2025 Mitchell Horner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Horner
-/
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# Bipartite graphs

This file proves results about bipartite simple graphs, including several double-counting arguments.

## Main definitions

* `SimpleGraph.IsBipartite G s t` is the condition that a simple graph `G` is bipartite in sets
  `s`, `t`, that is, `s` and `t` are disjoint and vertices `v`, `w` being adjacent in `G` implies
  that `v ∈ s` and `w ∈ t`, or `v ∈ s` and `w ∈ t`.

  Note that in this implementation, if `G.IsBipartite s t`, `s ∪ t` need not cover the vertices of
  `G`, instead `s ∪ t` is only required to cover the *support* of `G`, that is, the vertices that
  form edges in `G`. This definition is equivalent to the expected definition. If `s` and `t` do
  not cover all the vertices, one recovers a covering of all the vertices by unioning the missing
  vertices `(s ∪ t)ᶜ` to either `s` or `t`.

* `SimpleGraph.isBipartite_sum_degrees_eq` is the proof that if `G.IsBipartite s t`, then the sum
  of the degrees of the vertices in `s` is equal to the sum of the degrees of the vertices in `t`.

* `SimpleGraph.isBipartite_sum_degrees_eq_card_edges` is the proof that if `G.IsBipartite s t`,
  then sum of the degrees of the vertices in `s` is equal to the number of edges in `G`.
-/


open BigOperators Finset Fintype

namespace SimpleGraph

variable {V : Type*} {v w : V} {G : SimpleGraph V} {s t : Set V}

section IsBipartite

/-- `G` is bipartite in sets `s` and `t` iff `s` and `t` are disjoint and if vertices `v` and `w`
are adjacent in `G` then `v ∈ s` and `w ∈ t`, or `v ∈ t` and `w ∈ s`. -/
structure IsBipartite (G : SimpleGraph V) (s t : Set V) : Prop where
  disjoint : Disjoint s t
  mem_of_adj ⦃v w⦄ : G.Adj v w → v ∈ s ∧ w ∈ t ∨ v ∈ t ∧ w ∈ s

theorem IsBipartite.symm (h : G.IsBipartite s t) : G.IsBipartite t s where
  disjoint := h.disjoint.symm
  mem_of_adj v w hadj := by
    rw [@and_comm (v ∈ t) (w ∈ s), @and_comm (v ∈ s) (w ∈ t)]
    exact h.mem_of_adj hadj.symm

theorem isBipartite_comm :
  G.IsBipartite s t ↔ G.IsBipartite t s := ⟨IsBipartite.symm, IsBipartite.symm⟩

/-- If `G.IsBipartite s t` and `v ∈ s`, then if `v` is adjacent to `w` in `G` then `w ∈ t`. -/
theorem IsBipartite.mem_of_mem_adj (h : G.IsBipartite s t) (hv : v ∈ s) :
    G.Adj v w → w ∈ t := by
  intro hadj
  apply h.mem_of_adj at hadj
  have nhv : v ∉ t := Set.disjoint_left.mp h.disjoint hv
  simpa [hv, nhv] using hadj

/-- If `G.IsBipartite s t` and `v ∈ s`, then the neighbor set of `v` is the set of vertices in `t`
adjacent to `v` in `G`. -/
theorem isBipartite_neighborSet (h : G.IsBipartite s t) (hv : v ∈ s) :
    G.neighborSet v = { w ∈ t | G.Adj v w } := by
  ext w
  rw [mem_neighborSet, Set.mem_setOf_eq, iff_and_self]
  exact h.mem_of_mem_adj hv

/-- If `G.IsBipartite s t` and `v ∈ s`, then the neighbor set of `v` is a subset of `t`. -/
theorem isBipartite_neighborSet_subset (h : G.IsBipartite s t) (hv : v ∈ s) :
    G.neighborSet v ⊆ t := by
  rw [isBipartite_neighborSet h hv]
  exact Set.sep_subset t (G.Adj v ·)

/-- If `G.IsBipartite s t` and `v ∈ s`, then the neighbor set of `v` is disjoint to `s`. -/
theorem isBipartite_neighborSet_disjoint (h : G.IsBipartite s t) (hv : v ∈ s) :
    Disjoint (G.neighborSet v) s :=
  Set.disjoint_of_subset_left (isBipartite_neighborSet_subset h hv) h.disjoint.symm

/-- If `G.IsBipartite s t` and `w ∈ t`, then if `v` is adjacent to `w` in `G` then `v ∈ s`. -/
theorem IsBipartite.mem_of_mem_adj' (h : G.IsBipartite s t) (hw : w ∈ t) :
    G.Adj v w → v ∈ s := by
  intro hadj
  apply h.mem_of_adj at hadj
  have nhw : w ∉ s := Set.disjoint_right.mp h.disjoint hw
  simpa [hw, nhw] using hadj

/-- If `G.IsBipartite s t` and `w ∈ t`, then the neighbor set of `w` is the set of vertices in `s`
adjacent to `w` in `G`. -/
theorem isBipartite_neighborSet' (h : G.IsBipartite s t) (hw : w ∈ t) :
    G.neighborSet w = { v ∈ s | G.Adj v w } := by
  ext v
  rw [mem_neighborSet, adj_comm, Set.mem_setOf_eq, iff_and_self]
  exact h.mem_of_mem_adj' hw

/-- If `G.IsBipartite s t` and `w ∈ t`, then the neighbor set of `w` is a subset of `s`. -/
theorem isBipartite_neighborSet_subset' (h : G.IsBipartite s t) (hw : w ∈ t) :
    G.neighborSet w ⊆ s := by
  rw [isBipartite_neighborSet' h hw]
  exact Set.sep_subset s (G.Adj · w)

/-- If `G.IsBipartite s t`, then the support of `G` is a subset of `s ∪ t`. -/
theorem isBipartite_support_subset (h : G.IsBipartite s t) : G.support ⊆ s ∪ t := by
  intro v ⟨w, hadj⟩
  apply h.mem_of_adj at hadj
  tauto

/-- If `G.IsBipartite s t` and `w ∈ t`, then the neighbor set of `w` is disjoint to `t`. -/
theorem isBipartite_neighborSet_disjoint' (h : G.IsBipartite s t) (hw : w ∈ t) :
    Disjoint (G.neighborSet w) t :=
  Set.disjoint_of_subset_left (isBipartite_neighborSet_subset' h hw) h.disjoint

variable [Fintype V] {s t : Finset V} [DecidableRel G.Adj]

/-- If `G.IsBipartite s t` and `v ∈ s`, then the neighbor finset of `v` is the set of vertices in
`s` adjacent to `v` in `G`. -/
theorem isBipartite_neighborFinset (h : G.IsBipartite s t) (hv : v ∈ s) :
    G.neighborFinset v = t.filter (G.Adj v ·) := by
  ext w
  rw [mem_neighborFinset, mem_filter, iff_and_self]
  exact h.mem_of_mem_adj hv

/-- If `G.IsBipartite s t` and `v ∈ s`, then the neighbor finset of `v` is the set of vertices
"above" `v` according to the adjacency relation of `G`. -/
theorem isBipartite_bipartiteAbove (h : G.IsBipartite s t) (hv : v ∈ s) :
    G.neighborFinset v = bipartiteAbove G.Adj t v := by
  rw [isBipartite_neighborFinset h hv]
  rfl

/-- If `G.IsBipartite s t` and `v ∈ s`, then the neighbor finset of `v` is a subset of `s`. -/
theorem isBipartite_neighborFinset_subset (h : G.IsBipartite s t) (hv : v ∈ s) :
    G.neighborFinset v ⊆ t := by
  rw [isBipartite_neighborFinset h hv]
  exact filter_subset (G.Adj v ·) t

/-- If `G.IsBipartite s t` and `v ∈ s`, then the neighbor finset of `v` is disjoint to `s`. -/
theorem isBipartite_neighborFinset_disjoint (h : G.IsBipartite s t) (hv : v ∈ s) :
    Disjoint (G.neighborFinset v) s := by
  rw [neighborFinset_def, ←disjoint_coe, Set.coe_toFinset]
  exact isBipartite_neighborSet_disjoint h hv

/-- If `G.IsBipartite s t` and `v ∈ s`, then the degree of `v` in `G` is at most the size of `t`. -/
theorem isBipartite_degree_le (h : G.IsBipartite s t) (hv : v ∈ s) :
    G.degree v ≤ #t := by
  rw [←card_neighborFinset_eq_degree]
  exact card_le_card (isBipartite_neighborFinset_subset h hv)

/-- If `G.IsBipartite s t` and `w ∈ t`, then the neighbor finset of `w` is the set of vertices in
`s` adjacent to `w` in `G`. -/
theorem isBipartite_neighborFinset' (h : G.IsBipartite s t) (hw : w ∈ t) :
    G.neighborFinset w = s.filter (G.Adj · w) := by
  ext v
  rw [mem_neighborFinset, adj_comm, mem_filter, iff_and_self]
  exact h.mem_of_mem_adj' hw

/-- If `G.IsBipartite s t` and `w ∈ t`, then the neighbor finset of `w` is the set of vertices
"below" `w` according to the adjacency relation of `G`. -/
theorem isBipartite_bipartiteBelow (h : G.IsBipartite s t) (hw : w ∈ t) :
    G.neighborFinset w = bipartiteBelow G.Adj s w := by
  rw [isBipartite_neighborFinset' h hw]
  rfl

/-- If `G.IsBipartite s t` and `w ∈ t`, then the neighbor finset of `w` is a subset of `s`. -/
theorem isBipartite_neighborFinset_subset' (h : G.IsBipartite s t) (hw : w ∈ t) :
    G.neighborFinset w ⊆ s := by
  rw [isBipartite_neighborFinset' h hw]
  exact filter_subset (G.Adj · w) s

/-- If `G.IsBipartite s t` and `w ∈ t`, then the neighbor finset of `w` is disjoint to `t`. -/
theorem isBipartite_neighborFinset_disjoint' (h : G.IsBipartite s t) (hw : w ∈ t) :
    Disjoint (G.neighborFinset w) t := by
  rw [neighborFinset_def, ←disjoint_coe, Set.coe_toFinset]
  exact isBipartite_neighborSet_disjoint' h hw

/-- If `G.IsBipartite s t` and `w ∈ t`, then the degree of `w` in `G` is at most the size of `s`. -/
theorem isBipartite_degree_le' (h : G.IsBipartite s t) (hw : w ∈ t) :
    G.degree w ≤ #s := by
  rw [←card_neighborFinset_eq_degree]
  exact card_le_card (isBipartite_neighborFinset_subset' h hw)

/-- If `G.IsBipartite s t`, then the sum of the degrees of vertices in `s` is equal to the sum of
the degrees of vertices in `t`.

See `sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow`. -/
theorem isBipartite_sum_degrees_eq (h : G.IsBipartite s t) :
    ∑ v ∈ s, G.degree v = ∑ w ∈ t, G.degree w := by
  simp_rw [←sum_attach t, ←sum_attach s, ←card_neighborFinset_eq_degree]
  conv_lhs =>
    rhs; intro v
    rw [isBipartite_bipartiteAbove h v.prop]
  conv_rhs =>
    rhs; intro w
    rw [isBipartite_bipartiteBelow h w.prop]
  simp_rw [sum_attach s fun w ↦ #(bipartiteAbove G.Adj t w),
    sum_attach t fun v ↦ #(bipartiteBelow G.Adj s v)]
  exact sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow G.Adj

variable [DecidableEq V]

/-- The degree-sum formula only counting over the vertices that form edges.

See `SimpleGraph.sum_degrees_eq_twice_card_edges`. -/
theorem sum_degrees_support_eq_twice_card_edges :
    ∑ v ∈ G.support, G.degree v = 2 * #G.edgeFinset := by
  simp_rw [←sum_degrees_eq_twice_card_edges,
    ←sum_add_sum_compl G.support.toFinset, self_eq_add_right]
  apply Finset.sum_eq_zero
  intro v hv
  rw [degree_eq_zero_iff_not_mem_support]
  rwa [mem_compl, Set.mem_toFinset] at hv

lemma isBipartite_sum_degrees_eq_twice_card_edges (h : G.IsBipartite s t) :
    ∑ v ∈ s ∪ t, G.degree v = 2 * #G.edgeFinset := by
  have hsub : G.support ⊆ ↑s ∪ ↑t := isBipartite_support_subset h
  rw [←coe_union, ←Set.toFinset_subset] at hsub
  rw [←Finset.sum_subset hsub, ←sum_degrees_support_eq_twice_card_edges]
  intro v _ hv
  rwa [Set.mem_toFinset, ←degree_eq_zero_iff_not_mem_support] at hv

/-- The degree-sum formula for bipartite graphs.

See `SimpleGraph.sum_degrees_eq_twice_card_edges`. -/
theorem isBipartite_sum_degrees_eq_card_edges (h : G.IsBipartite s t) :
    ∑ v ∈ s, G.degree v = #G.edgeFinset := by
  rw [←Nat.mul_left_cancel_iff zero_lt_two, ←isBipartite_sum_degrees_eq_twice_card_edges h,
    sum_union (disjoint_coe.mp h.disjoint), two_mul, add_right_inj]
  exact isBipartite_sum_degrees_eq h

/-- The degree-sum formula for bipartite graphs.

See `SimpleGraph.sum_degrees_eq_twice_card_edges`. -/
theorem isBipartite_sum_degrees_eq_card_edges' (h : G.IsBipartite s t) :
    ∑ v ∈ t, G.degree v = #G.edgeFinset := isBipartite_sum_degrees_eq_card_edges h.symm

end IsBipartite

end SimpleGraph
