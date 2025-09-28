/-
Copyright (c) 2025 Mitchell Horner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Horner
-/
import Mathlib.Algebra.Notation.Indicator
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# Bipartite graphs

This file proves results about bipartite simple graphs, including several double-counting arguments.

## Main definitions

* `SimpleGraph.IsBipartiteWith G s t` is the condition that a simple graph `G` is bipartite in sets
  `s`, `t`, that is, `s` and `t` are disjoint and vertices `v`, `w` being adjacent in `G` implies
  that `v ∈ s` and `w ∈ t`, or `v ∈ s` and `w ∈ t`.

  Note that in this implementation, if `G.IsBipartiteWith s t`, `s ∪ t` need not cover the vertices
  of `G`, instead `s ∪ t` is only required to cover the *support* of `G`, that is, the vertices
  that form edges in `G`. This definition is equivalent to the expected definition. If `s` and `t`
  do not cover all the vertices, one recovers a covering of all the vertices by unioning the
  missing vertices `(s ∪ t)ᶜ` to either `s` or `t`.

* `SimpleGraph.IsBipartite`: Predicate for a simple graph to be bipartite.
  `G.IsBipartite` is defined as an abbreviation for `G.Colorable 2`.

* `SimpleGraph.isBipartite_iff_exists_isBipartiteWith` is the proof that `G.IsBipartite` iff
  `G.IsBipartiteWith s t`.

* `SimpleGraph.isBipartiteWith_sum_degrees_eq` is the proof that if `G.IsBipartiteWith s t`, then
  the sum of the degrees of the vertices in `s` is equal to the sum of the degrees of the vertices
  in `t`.

* `SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges` is the proof that if
  `G.IsBipartiteWith s t`, then sum of the degrees of the vertices in `s` is equal to the number of
  edges in `G`.

  See `SimpleGraph.sum_degrees_eq_twice_card_edges` for the general version, and
  `SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges'` for the version from the "right".

## Implementation notes

For the formulation of double-counting arguments where a bipartite graph is considered as a
relation `r : α → β → Prop`, see `Mathlib/Combinatorics/Enumerative/DoubleCounting.lean`.

## TODO

* Prove that `G.IsBipartite` iff `G` does not contain an odd cycle.
  I.e., `G.IsBipartite ↔ ∀ n, (cycleGraph (2*n+1)).Free G`.
-/


open BigOperators Finset Fintype

namespace SimpleGraph

variable {V : Type*} {v w : V} {G : SimpleGraph V} {s t : Set V}

section IsBipartiteWith

/-- `G` is bipartite in sets `s` and `t` iff `s` and `t` are disjoint and if vertices `v` and `w`
are adjacent in `G` then `v ∈ s` and `w ∈ t`, or `v ∈ t` and `w ∈ s`. -/
structure IsBipartiteWith (G : SimpleGraph V) (s t : Set V) : Prop where
  disjoint : Disjoint s t
  mem_of_adj ⦃v w : V⦄ : G.Adj v w → v ∈ s ∧ w ∈ t ∨ v ∈ t ∧ w ∈ s

theorem IsBipartiteWith.symm (h : G.IsBipartiteWith s t) : G.IsBipartiteWith t s where
  disjoint := h.disjoint.symm
  mem_of_adj v w hadj := by
    rw [@and_comm (v ∈ t) (w ∈ s), @and_comm (v ∈ s) (w ∈ t)]
    exact h.mem_of_adj hadj.symm

theorem isBipartiteWith_comm : G.IsBipartiteWith s t ↔ G.IsBipartiteWith t s :=
  ⟨IsBipartiteWith.symm, IsBipartiteWith.symm⟩

/-- If `G.IsBipartiteWith s t` and `v ∈ s`, then if `v` is adjacent to `w` in `G` then `w ∈ t`. -/
theorem IsBipartiteWith.mem_of_mem_adj
    (h : G.IsBipartiteWith s t) (hv : v ∈ s) (hadj : G.Adj v w) : w ∈ t := by
  apply h.mem_of_adj at hadj
  have nhv : v ∉ t := Set.disjoint_left.mp h.disjoint hv
  simpa [hv, nhv] using hadj

/-- If `G.IsBipartiteWith s t` and `v ∈ s`, then the neighbor set of `v` is the set of vertices in
`t` adjacent to `v` in `G`. -/
theorem isBipartiteWith_neighborSet (h : G.IsBipartiteWith s t) (hv : v ∈ s) :
    G.neighborSet v = { w ∈ t | G.Adj v w } := by
  ext w
  rw [mem_neighborSet, Set.mem_setOf_eq, iff_and_self]
  exact h.mem_of_mem_adj hv

/-- If `G.IsBipartiteWith s t` and `v ∈ s`, then the neighbor set of `v` is a subset of `t`. -/
theorem isBipartiteWith_neighborSet_subset (h : G.IsBipartiteWith s t) (hv : v ∈ s) :
    G.neighborSet v ⊆ t := by
  rw [isBipartiteWith_neighborSet h hv]
  exact Set.sep_subset t (G.Adj v ·)

/-- If `G.IsBipartiteWith s t` and `v ∈ s`, then the neighbor set of `v` is disjoint to `s`. -/
theorem isBipartiteWith_neighborSet_disjoint (h : G.IsBipartiteWith s t) (hv : v ∈ s) :
    Disjoint (G.neighborSet v) s :=
  Set.disjoint_of_subset_left (isBipartiteWith_neighborSet_subset h hv) h.disjoint.symm

/-- If `G.IsBipartiteWith s t` and `w ∈ t`, then if `v` is adjacent to `w` in `G` then `v ∈ s`. -/
theorem IsBipartiteWith.mem_of_mem_adj'
    (h : G.IsBipartiteWith s t) (hw : w ∈ t) (hadj : G.Adj v w) : v ∈ s := by
  apply h.mem_of_adj at hadj
  have nhw : w ∉ s := Set.disjoint_right.mp h.disjoint hw
  simpa [hw, nhw] using hadj

/-- If `G.IsBipartiteWith s t` and `w ∈ t`, then the neighbor set of `w` is the set of vertices in
`s` adjacent to `w` in `G`. -/
theorem isBipartiteWith_neighborSet' (h : G.IsBipartiteWith s t) (hw : w ∈ t) :
    G.neighborSet w = { v ∈ s | G.Adj v w } := by
  ext v
  rw [mem_neighborSet, adj_comm, Set.mem_setOf_eq, iff_and_self]
  exact h.mem_of_mem_adj' hw

/-- If `G.IsBipartiteWith s t` and `w ∈ t`, then the neighbor set of `w` is a subset of `s`. -/
theorem isBipartiteWith_neighborSet_subset' (h : G.IsBipartiteWith s t) (hw : w ∈ t) :
    G.neighborSet w ⊆ s := by
  rw [isBipartiteWith_neighborSet' h hw]
  exact Set.sep_subset s (G.Adj · w)

/-- If `G.IsBipartiteWith s t`, then the support of `G` is a subset of `s ∪ t`. -/
theorem isBipartiteWith_support_subset (h : G.IsBipartiteWith s t) : G.support ⊆ s ∪ t := by
  intro v ⟨w, hadj⟩
  apply h.mem_of_adj at hadj
  tauto

/-- If `G.IsBipartiteWith s t` and `w ∈ t`, then the neighbor set of `w` is disjoint to `t`. -/
theorem isBipartiteWith_neighborSet_disjoint' (h : G.IsBipartiteWith s t) (hw : w ∈ t) :
    Disjoint (G.neighborSet w) t :=
  Set.disjoint_of_subset_left (isBipartiteWith_neighborSet_subset' h hw) h.disjoint

variable {s t : Finset V} [DecidableRel G.Adj]

section

variable [Fintype ↑(G.neighborSet v)] [Fintype ↑(G.neighborSet w)]

/-- If `G.IsBipartiteWith s t` and `v ∈ s`, then the neighbor finset of `v` is the set of vertices
in `s` adjacent to `v` in `G`. -/
theorem isBipartiteWith_neighborFinset (h : G.IsBipartiteWith s t) (hv : v ∈ s) :
    G.neighborFinset v = { w ∈ t | G.Adj v w } := by
  ext w
  rw [mem_neighborFinset, mem_filter, iff_and_self]
  exact h.mem_of_mem_adj hv

/-- If `G.IsBipartiteWith s t` and `v ∈ s`, then the neighbor finset of `v` is the set of vertices
"above" `v` according to the adjacency relation of `G`. -/
theorem isBipartiteWith_bipartiteAbove (h : G.IsBipartiteWith s t) (hv : v ∈ s) :
    G.neighborFinset v = bipartiteAbove G.Adj t v := by
  rw [isBipartiteWith_neighborFinset h hv, bipartiteAbove]

/-- If `G.IsBipartiteWith s t` and `v ∈ s`, then the neighbor finset of `v` is a subset of `s`. -/
theorem isBipartiteWith_neighborFinset_subset (h : G.IsBipartiteWith s t) (hv : v ∈ s) :
    G.neighborFinset v ⊆ t := by
  rw [isBipartiteWith_neighborFinset h hv]
  exact filter_subset (G.Adj v ·) t

omit [DecidableRel G.Adj] in
/-- If `G.IsBipartiteWith s t` and `v ∈ s`, then the neighbor finset of `v` is disjoint to `s`. -/
theorem isBipartiteWith_neighborFinset_disjoint (h : G.IsBipartiteWith s t) (hv : v ∈ s) :
    Disjoint (G.neighborFinset v) s := by
  rw [neighborFinset_def, ← disjoint_coe, Set.coe_toFinset]
  exact isBipartiteWith_neighborSet_disjoint h hv

/-- If `G.IsBipartiteWith s t` and `v ∈ s`, then the degree of `v` in `G` is at most the size of
`t`. -/
theorem isBipartiteWith_degree_le (h : G.IsBipartiteWith s t) (hv : v ∈ s) : G.degree v ≤ #t := by
  rw [← card_neighborFinset_eq_degree]
  exact card_le_card (isBipartiteWith_neighborFinset_subset h hv)

/-- If `G.IsBipartiteWith s t` and `w ∈ t`, then the neighbor finset of `w` is the set of vertices
in `s` adjacent to `w` in `G`. -/
theorem isBipartiteWith_neighborFinset' (h : G.IsBipartiteWith s t) (hw : w ∈ t) :
    G.neighborFinset w = { v ∈ s | G.Adj v w } := by
  ext v
  rw [mem_neighborFinset, adj_comm, mem_filter, iff_and_self]
  exact h.mem_of_mem_adj' hw

/-- If `G.IsBipartiteWith s t` and `w ∈ t`, then the neighbor finset of `w` is the set of vertices
"below" `w` according to the adjacency relation of `G`. -/
theorem isBipartiteWith_bipartiteBelow (h : G.IsBipartiteWith s t) (hw : w ∈ t) :
    G.neighborFinset w = bipartiteBelow G.Adj s w := by
  rw [isBipartiteWith_neighborFinset' h hw, bipartiteBelow]

/-- If `G.IsBipartiteWith s t` and `w ∈ t`, then the neighbor finset of `w` is a subset of `s`. -/
theorem isBipartiteWith_neighborFinset_subset' (h : G.IsBipartiteWith s t) (hw : w ∈ t) :
    G.neighborFinset w ⊆ s := by
  rw [isBipartiteWith_neighborFinset' h hw]
  exact filter_subset (G.Adj · w) s

omit [DecidableRel G.Adj] in
/-- If `G.IsBipartiteWith s t` and `w ∈ t`, then the neighbor finset of `w` is disjoint to `t`. -/
theorem isBipartiteWith_neighborFinset_disjoint' (h : G.IsBipartiteWith s t) (hw : w ∈ t) :
    Disjoint (G.neighborFinset w) t := by
  rw [neighborFinset_def, ← disjoint_coe, Set.coe_toFinset]
  exact isBipartiteWith_neighborSet_disjoint' h hw

/-- If `G.IsBipartiteWith s t` and `w ∈ t`, then the degree of `w` in `G` is at most the size of
`s`. -/
theorem isBipartiteWith_degree_le' (h : G.IsBipartiteWith s t) (hw : w ∈ t) : G.degree w ≤ #s := by
  rw [← card_neighborFinset_eq_degree]
  exact card_le_card (isBipartiteWith_neighborFinset_subset' h hw)

end

/-- If `G.IsBipartiteWith s t`, then the sum of the degrees of vertices in `s` is equal to the sum
of the degrees of vertices in `t`.

See `Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow`. -/
theorem isBipartiteWith_sum_degrees_eq [G.LocallyFinite] (h : G.IsBipartiteWith s t) :
    ∑ v ∈ s, G.degree v = ∑ w ∈ t, G.degree w := by
  simp_rw [← sum_attach t, ← sum_attach s, ← card_neighborFinset_eq_degree]
  conv_lhs =>
    rhs; intro v
    rw [isBipartiteWith_bipartiteAbove h v.prop]
  conv_rhs =>
    rhs; intro w
    rw [isBipartiteWith_bipartiteBelow h w.prop]
  simp_rw [sum_attach s fun w ↦ #(bipartiteAbove G.Adj t w),
    sum_attach t fun v ↦ #(bipartiteBelow G.Adj s v)]
  exact sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow G.Adj

variable [Fintype V]

lemma isBipartiteWith_sum_degrees_eq_twice_card_edges [DecidableEq V] (h : G.IsBipartiteWith s t) :
    ∑ v ∈ s ∪ t, G.degree v = 2 * #G.edgeFinset := by
  have hsub : G.support ⊆ ↑s ∪ ↑t := isBipartiteWith_support_subset h
  rw [← coe_union, ← Set.toFinset_subset] at hsub
  rw [← Finset.sum_subset hsub, ← sum_degrees_support_eq_twice_card_edges]
  intro v _ hv
  rwa [Set.mem_toFinset, ← degree_eq_zero_iff_notMem_support] at hv

/-- The degree-sum formula for bipartite graphs, summing over the "left" part.

See `SimpleGraph.sum_degrees_eq_twice_card_edges` for the general version, and
`SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges'` for the version from the "right". -/
theorem isBipartiteWith_sum_degrees_eq_card_edges (h : G.IsBipartiteWith s t) :
    ∑ v ∈ s, G.degree v = #G.edgeFinset := by
  classical
  rw [← Nat.mul_left_cancel_iff zero_lt_two, ← isBipartiteWith_sum_degrees_eq_twice_card_edges h,
    sum_union (disjoint_coe.mp h.disjoint), two_mul, add_right_inj]
  exact isBipartiteWith_sum_degrees_eq h

/-- The degree-sum formula for bipartite graphs, summing over the "right" part.

See `SimpleGraph.sum_degrees_eq_twice_card_edges` for the general version, and
`SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges` for the version from the "left". -/
theorem isBipartiteWith_sum_degrees_eq_card_edges' (h : G.IsBipartiteWith s t) :
    ∑ v ∈ t, G.degree v = #G.edgeFinset := isBipartiteWith_sum_degrees_eq_card_edges h.symm

end IsBipartiteWith

section IsBipartite

/-- The predicate for a simple graph to be bipartite. -/
abbrev IsBipartite (G : SimpleGraph V) : Prop := G.Colorable 2

/-- If a simple graph `G` is bipartite, then there exist disjoint sets `s` and `t`
such that all edges in `G` connect a vertex in `s` to a vertex in `t`. -/
lemma IsBipartite.exists_isBipartiteWith (h : G.IsBipartite) : ∃ s t, G.IsBipartiteWith s t := by
  obtain ⟨c, hc⟩ := h
  refine ⟨{v | c v = 0}, {v | c v = 1}, by aesop (add simp [Set.disjoint_left]), ?_⟩
  rintro v w hvw
  apply hc at hvw
  simp [Set.mem_setOf_eq] at hvw ⊢
  cutsat

/-- If a simple graph `G` has a bipartition, then it is bipartite. -/
lemma IsBipartiteWith.isBipartite {s t : Set V} (h : G.IsBipartiteWith s t) : G.IsBipartite := by
  refine ⟨s.indicator 1, fun {v w} hw ↦ ?_⟩
  obtain (⟨hs, ht⟩ | ⟨ht, hs⟩) := h.2 hw <;>
    { replace ht : _ ∉ s := h.1.subset_compl_left ht; simp [hs, ht] }

/-- `G.IsBipartite` if and only if `G.IsBipartiteWith s t`. -/
theorem isBipartite_iff_exists_isBipartiteWith :
    G.IsBipartite ↔ ∃ s t : Set V, G.IsBipartiteWith s t :=
  ⟨IsBipartite.exists_isBipartiteWith, fun ⟨_, _, h⟩ ↦ h.isBipartite⟩

end IsBipartite

section CompleteBipartiteSubgraph

variable {α β : Type*} [Fintype α] [Fintype β]

/-- A complete bipartite subgraph of `s` and `t` parts is a "left" subset of `s` vertices and a
"right" subset of `t` vertices such that every vertex in the "left" subset is adjacent to every
vertex in the "right" subset. -/
structure CompleteBipartiteSubgraph (G : SimpleGraph V) (s t : ℕ) where
  /-- The "left" subset is size `s`. -/
  left : Finset V
  card_left : #left = s
  /-- The "right" subset of size `t`. -/
  right : Finset V
  card_right : #right = t
  /-- Vertices in the "left" and "right" subsets are adjacent. -/
  Adj : ∀ ⦃v₁⦄, v₁ ∈ left → ∀ ⦃v₂⦄, v₂ ∈ right → G.Adj v₁ v₂

variable {s t : ℕ} (B : G.CompleteBipartiteSubgraph s t)

namespace CompleteBipartiteSubgraph

/-- The "left" and "right" parts in a `G.CompleteBipartiteSubgraph s t` are disjoint. -/
theorem disjoint_left_right : Disjoint B.left B.right :=
  disjoint_left.mpr fun v hv₁ hv₂ ↦ (G.loopless v) (B.Adj hv₁ hv₂)

/-- The finset of vertices in a `G.CompleteBipartiteSubgraph s t`. -/
@[simp]
abbrev verts : Finset V := disjUnion B.left B.right B.disjoint_left_right

/-- There are `s + t` vertices in a complete bipartite subgraph with `s` vertices in the "left"
part and `t` vertices in the "right" part. -/
theorem card_verts : #B.verts = s + t := by simp [card_left, card_right]

/-- A complete bipartite subgraph gives rise to a copy of a complete bipartite graph. -/
noncomputable def toCopy : Copy (completeBipartiteGraph (Fin s) (Fin t)) G := by
  have : Nonempty (Fin s ↪ B.left) := by
    apply Function.Embedding.nonempty_of_card_le
    rw [Fintype.card_fin, card_coe, card_left]
  let fs : Fin s ↪ B.left := Classical.arbitrary (Fin s ↪ B.left)
  have : Nonempty (Fin t ↪ B.right) := by
    apply Function.Embedding.nonempty_of_card_le
    rw [Fintype.card_fin, card_coe, card_right]
  let ft : Fin t ↪ B.right := Classical.arbitrary (Fin t ↪ B.right)
  let f : Fin s ⊕ Fin t ↪ V := by
    refine ⟨Sum.elim (Subtype.val ∘ fs) (Subtype.val ∘ ft), fun st₁ st₂ ↦ ?_⟩
    match st₁, st₂ with
    | Sum.inl s₁, Sum.inl s₂ => simp [← Subtype.ext_iff]
    | Sum.inr t₁, Sum.inl s₂ =>
      simpa using (B.Adj (fs s₂).prop (ft t₁).prop).ne'
    | Sum.inl s₁, Sum.inr t₂ =>
      simpa using (B.Adj (fs s₁).prop (ft t₂).prop).symm.ne'
    | Sum.inr t₁, Sum.inr t₂ => simp [← Subtype.ext_iff]
  refine ⟨⟨f.toFun, fun {st₁ st₂} hadj ↦ ?_⟩, f.injective⟩
  rcases hadj with ⟨hst₁, hst₂⟩ | ⟨hst₁, hst₂⟩
  all_goals dsimp [f]
  · rw [← Sum.inl_getLeft st₁ hst₁, ← Sum.inr_getRight st₂ hst₂,
      Sum.elim_inl, Sum.elim_inr]
    exact B.Adj (by simp) (by simp)
  · rw [← Sum.inr_getRight st₁ hst₁, ← Sum.inl_getLeft st₂ hst₂,
      Sum.elim_inl, Sum.elim_inr, adj_comm]
    exact B.Adj (by simp) (by simp)

/-- A copy of a complete bipartite graph identifies a complete bipartite subgraph. -/
def ofCopy (f : Copy (completeBipartiteGraph α β) G) :
    G.CompleteBipartiteSubgraph (card α) (card β) where
  left := univ.map ⟨f ∘ Sum.inl, f.injective.comp Sum.inl_injective⟩
  card_left := by rw [card_map, card_univ]
  right := univ.map ⟨f ∘ Sum.inr, f.injective.comp Sum.inr_injective⟩
  card_right := by rw [card_map, card_univ]
  Adj _ h₁ _ h₂ := by
    rw [mem_map] at h₁ h₂
    obtain ⟨_, _, h₁⟩ := h₁
    obtain ⟨_, _, h₂⟩ := h₂
    rw [← h₁, ← h₂]
    exact f.toHom.map_adj (by simp)

end CompleteBipartiteSubgraph

/-- Simple graphs contain a copy of a `completeBipartiteGraph α β` iff
`G.CompleteBipartiteSubgraph (card α) (card β)` is nonempty. -/
theorem completeBipartiteGraph_isContained_iff :
    completeBipartiteGraph α β ⊑ G ↔ Nonempty (G.CompleteBipartiteSubgraph (card α) (card β)) :=
  ⟨fun ⟨f⟩ ↦ ⟨CompleteBipartiteSubgraph.ofCopy f⟩,
    fun ⟨B⟩ ↦ ⟨B.toCopy.comp <| Iso.toCopy ⟨(equivFin α).sumCongr (equivFin β), by simp⟩⟩⟩

end CompleteBipartiteSubgraph

end SimpleGraph
