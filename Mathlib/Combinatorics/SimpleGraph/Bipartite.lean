/-
Copyright (c) 2025 Mitchell Horner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Horner
-/
module

public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Combinatorics.SimpleGraph.Coloring
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum

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

* `SimpleGraph.completeBipartiteGraph_isContained_iff` is the proof that simple graphs contain a
  copy of a `completeBipartiteGraph α β` iff there exists a "left" subset of `card α` vertices and
  a "right" subset of `card β` vertices such that every vertex in the "left" subset is adjacent to
  every vertex in the "right" subset.

* `SimpleGraph.between`; the simple graph `G.between s t` is the subgraph of `G` containing edges
  that connect a vertex in the set `s` to a vertex in the set `t`.

## Implementation notes

For the formulation of double-counting arguments where a bipartite graph is considered as a
relation `r : α → β → Prop`, see `Mathlib/Combinatorics/Enumerative/DoubleCounting.lean`.

## TODO

* Prove that `G.IsBipartite` iff `G` does not contain an odd cycle.
  I.e., `G.IsBipartite ↔ ∀ n, (cycleGraph (2*n+1)).Free G`.
-/

@[expose] public section


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

variable {s t : Finset V}

section

variable [Fintype ↑(G.neighborSet v)] [Fintype ↑(G.neighborSet w)]

section decidableRel

variable [DecidableRel G.Adj]

/-- If `G.IsBipartiteWith s t` and `v ∈ s`, then the neighbor finset of `v` is the set of vertices
in `s` adjacent to `v` in `G`. -/
theorem isBipartiteWith_neighborFinset (h : G.IsBipartiteWith s t) (hv : v ∈ s) :
    G.neighborFinset v = { w ∈ t | G.Adj v w } := by
  ext w
  rw [mem_neighborFinset, mem_filter, iff_and_self]
  exact h.mem_of_mem_adj hv

/-- If `G.IsBipartiteWith s t` and `w ∈ t`, then the neighbor finset of `w` is the set of vertices
in `s` adjacent to `w` in `G`. -/
theorem isBipartiteWith_neighborFinset' (h : G.IsBipartiteWith s t) (hw : w ∈ t) :
    G.neighborFinset w = { v ∈ s | G.Adj v w } := by
  ext v
  rw [mem_neighborFinset, adj_comm, mem_filter, iff_and_self]
  exact h.mem_of_mem_adj' hw

/-- If `G.IsBipartiteWith s t` and `v ∈ s`, then the neighbor finset of `v` is the set of vertices
"above" `v` according to the adjacency relation of `G`. -/
theorem isBipartiteWith_bipartiteAbove (h : G.IsBipartiteWith s t) (hv : v ∈ s) :
    G.neighborFinset v = bipartiteAbove G.Adj t v := by
  rw [isBipartiteWith_neighborFinset h hv, bipartiteAbove]

/-- If `G.IsBipartiteWith s t` and `w ∈ t`, then the neighbor finset of `w` is the set of vertices
"below" `w` according to the adjacency relation of `G`. -/
theorem isBipartiteWith_bipartiteBelow (h : G.IsBipartiteWith s t) (hw : w ∈ t) :
    G.neighborFinset w = bipartiteBelow G.Adj s w := by
  rw [isBipartiteWith_neighborFinset' h hw, bipartiteBelow]

end decidableRel

/-- If `G.IsBipartiteWith s t` and `v ∈ s`, then the neighbor finset of `v` is a subset of `s`. -/
theorem isBipartiteWith_neighborFinset_subset (h : G.IsBipartiteWith s t) (hv : v ∈ s) :
    G.neighborFinset v ⊆ t := by
  classical
  rw [isBipartiteWith_neighborFinset h hv]
  exact filter_subset (G.Adj v ·) t

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

/-- If `G.IsBipartiteWith s t` and `w ∈ t`, then the neighbor finset of `w` is a subset of `s`. -/
theorem isBipartiteWith_neighborFinset_subset' (h : G.IsBipartiteWith s t) (hw : w ∈ t) :
    G.neighborFinset w ⊆ s := by
  classical
  rw [isBipartiteWith_neighborFinset' h hw]
  exact filter_subset (G.Adj · w) s

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
  classical
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

variable [Fintype V] [DecidableRel G.Adj]

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
  lia

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

section Copy

variable {α β : Type*} [Fintype α] [Fintype β]

/-- A "left" subset of `card α` vertices and a "right" subset of `card β` vertices such that every
vertex in the "left" subset is adjacent to every vertex in the "right" subset gives rise to a copy
of a complete bipartite graph. -/
noncomputable def Copy.completeBipartiteGraph
    (left right : Finset V) (card_left : #left = card α) (card_right : #right = card β)
    (h : G.IsCompleteBetween left right) : Copy (completeBipartiteGraph α β) G := by
  have : Nonempty (α ↪ left) := by
    rw [← card_coe] at card_left
    exact Function.Embedding.nonempty_of_card_le card_left.symm.le
  let fα : α ↪ left := Classical.arbitrary (α ↪ left)
  have : Nonempty (β ↪ right) := by
    rw [← card_coe] at card_right
    exact Function.Embedding.nonempty_of_card_le card_right.symm.le
  let fβ : β ↪ right := Classical.arbitrary (β ↪ right)
  let f : α ⊕ β ↪ V := by
    refine ⟨Sum.elim (Subtype.val ∘ fα) (Subtype.val ∘ fβ), fun s₁ s₂ ↦ ?_⟩
    match s₁, s₂ with
    | .inl p₁, .inl p₂ => simp
    | .inr p₁, .inl p₂ =>
      simpa using (h (fα p₂).prop (fβ p₁).prop).ne'
    | .inl p₁, .inr p₂ =>
      simpa using (h (fα p₁).prop (fβ p₂).prop).symm.ne'
    | .inr p₁, .inr p₂ => simp
  refine ⟨⟨f.toFun, fun {s₁ s₂} hadj ↦ ?_⟩, f.injective⟩
  rcases hadj with ⟨hs₁, hs₂⟩ | ⟨hs₁, hs₂⟩
  all_goals dsimp [f]
  · rw [← Sum.inl_getLeft s₁ hs₁, ← Sum.inr_getRight s₂ hs₂,
      Sum.elim_inl, Sum.elim_inr]
    exact h (by simp) (by simp)
  · rw [← Sum.inr_getRight s₁ hs₁, ← Sum.inl_getLeft s₂ hs₂,
      Sum.elim_inl, Sum.elim_inr, adj_comm]
    exact h (by simp) (by simp)

/-- Simple graphs contain a copy of a `completeBipartiteGraph α β` iff there exists a "left"
subset of `card α` vertices and a "right" subset of `card β` vertices such that every vertex
in the "left" subset is adjacent to every vertex in the "right" subset. -/
theorem completeBipartiteGraph_isContained_iff :
    completeBipartiteGraph α β ⊑ G ↔
      ∃ (left right : Finset V), #left = card α ∧ #right = card β
        ∧ G.IsCompleteBetween left right where
  mp := by
    refine fun ⟨f⟩ ↦ ⟨univ.map ⟨f ∘ Sum.inl, f.injective.comp Sum.inl_injective⟩,
      univ.map ⟨f ∘ Sum.inr, f.injective.comp Sum.inr_injective⟩, by simp, by simp,
      fun _ hl _ hr ↦ ?_⟩
    rw [mem_coe, mem_map] at hl hr
    replace ⟨_, _, hl⟩ := hl
    replace ⟨_, _, hr⟩ := hr
    rw [← hl, ← hr]
    exact f.toHom.map_adj (by simp)
  mpr := fun ⟨left, right, card_left, card_right, h⟩ ↦
    ⟨.completeBipartiteGraph left right card_left card_right h⟩

end Copy

section Between

/-- The subgraph of `G` containing edges that connect a vertex in the set `s` to a vertex in the
set `t`. -/
def between (s t : Set V) (G : SimpleGraph V) : SimpleGraph V where
  Adj v w := G.Adj v w ∧ (v ∈ s ∧ w ∈ t ∨ v ∈ t ∧ w ∈ s)
  symm v w := by tauto

lemma between_adj : (G.between s t).Adj v w ↔ G.Adj v w ∧ (v ∈ s ∧ w ∈ t ∨ v ∈ t ∧ w ∈ s) := by rfl

lemma between_le : G.between s t ≤ G := fun _ _ h ↦ h.1

lemma between_comm : G.between s t = G.between t s := by simp [between, or_comm]

instance [DecidableRel G.Adj] [DecidablePred (· ∈ s)] [DecidablePred (· ∈ t)] :
    DecidableRel (G.between s t).Adj :=
  inferInstanceAs (DecidableRel fun v w ↦ G.Adj v w ∧ (v ∈ s ∧ w ∈ t ∨ v ∈ t ∧ w ∈ s))

/-- `G.between s t` is bipartite if the sets `s` and `t` are disjoint. -/
theorem between_isBipartiteWith (h : Disjoint s t) : (G.between s t).IsBipartiteWith s t where
  disjoint := h
  mem_of_adj _ _ h := h.2

/-- `G.between s t` is bipartite if the sets `s` and `t` are disjoint. -/
theorem between_isBipartite (h : Disjoint s t) : (G.between s t).IsBipartite :=
  (between_isBipartiteWith h).isBipartite

/-- The neighbor set of `v ∈ s` in `G.between s sᶜ` excludes the vertices in `s` adjacent to `v`
in `G`. -/
lemma neighborSet_subset_between_union (hv : v ∈ s) :
    G.neighborSet v ⊆ (G.between s sᶜ).neighborSet v ∪ s := by
  intro w hadj
  rw [neighborSet, Set.mem_union, Set.mem_setOf, between_adj]
  by_cases hw : w ∈ s
  · exact Or.inr hw
  · exact Or.inl ⟨hadj, Or.inl ⟨hv, hw⟩⟩

/-- The neighbor set of `w ∈ sᶜ` in `G.between s sᶜ` excludes the vertices in `sᶜ` adjacent to `w`
in `G`. -/
lemma neighborSet_subset_between_union_compl (hw : w ∈ sᶜ) :
    G.neighborSet w ⊆ (G.between s sᶜ).neighborSet w ∪ sᶜ := by
  intro v hadj
  rw [neighborSet, Set.mem_union, Set.mem_setOf, between_adj]
  by_cases hv : v ∈ s
  · exact Or.inl ⟨hadj, Or.inr ⟨hw, hv⟩⟩
  · exact Or.inr hv

variable [DecidableEq V] [Fintype V] {s t : Finset V} [DecidableRel G.Adj]

/-- The neighbor finset of `v ∈ s` in `G.between s sᶜ` excludes the vertices in `s` adjacent to `v`
in `G`. -/
lemma neighborFinset_subset_between_union (hv : v ∈ s) :
    G.neighborFinset v ⊆ (G.between s sᶜ).neighborFinset v ∪ s := by
  simpa [neighborFinset_def] using neighborSet_subset_between_union hv

/-- The degree of `v ∈ s` in `G` is at most the degree in `G.between s sᶜ` plus the excluded
vertices from `s`. -/
theorem degree_le_between_add (hv : v ∈ s) :
    G.degree v ≤ (G.between s sᶜ).degree v + s.card := by
  have h_bipartite : (G.between s sᶜ).IsBipartiteWith s ↑(sᶜ) := by
    simpa using between_isBipartiteWith disjoint_compl_right
  simp_rw [← card_neighborFinset_eq_degree,
    ← card_union_of_disjoint (isBipartiteWith_neighborFinset_disjoint h_bipartite hv)]
  exact card_le_card (neighborFinset_subset_between_union hv)

/-- The neighbor finset of `w ∈ sᶜ` in `G.between s sᶜ` excludes the vertices in `sᶜ` adjacent to
`w` in `G`. -/
lemma neighborFinset_subset_between_union_compl (hw : w ∈ sᶜ) :
    G.neighborFinset w ⊆ (G.between s sᶜ).neighborFinset w ∪ sᶜ := by
  simpa [neighborFinset_def] using G.neighborSet_subset_between_union_compl (by simpa using hw)

/-- The degree of `w ∈ sᶜ` in `G` is at most the degree in `G.between s sᶜ` plus the excluded
vertices from `sᶜ`. -/
theorem degree_le_between_add_compl (hw : w ∈ sᶜ) :
    G.degree w ≤ (G.between s sᶜ).degree w + sᶜ.card := by
  have h_bipartite : (G.between s sᶜ).IsBipartiteWith s ↑(sᶜ) := by
    simpa using between_isBipartiteWith disjoint_compl_right
  simp_rw [← card_neighborFinset_eq_degree,
    ← card_union_of_disjoint (isBipartiteWith_neighborFinset_disjoint' h_bipartite hw)]
  exact card_le_card (neighborFinset_subset_between_union_compl hw)

end Between

section

variable {V : Type*} {G : SimpleGraph V}

private lemma delete_incidence_set_is_bipartite_with_of_is_bipartite_with {s t : Finset V} {a : V}
    (hG : G.IsBipartiteWith (insert a ↑s) ↑t) :
    (G.deleteIncidenceSet a).IsBipartiteWith ↑s ↑t := by
  constructor
  · have h₀ := hG.disjoint
    simp only [Set.disjoint_insert_left, SetLike.mem_coe, Finset.disjoint_coe] at h₀
    simp only [Finset.disjoint_coe]; exact h₀.2
  · intros x y hxy; simp only [SetLike.mem_coe]
    have h₀ := hG.mem_of_adj
    simp only [Set.mem_insert_iff, SetLike.mem_coe] at h₀
    rw [G.deleteIncidenceSet_adj] at hxy; grind

private lemma edgeSet_decompose (a : V) :
    G.edgeSet = (G.deleteIncidenceSet a).edgeSet ∪ G.incidenceSet a := by
  symm; rw [edgeSet_deleteIncidenceSet];
  simp only [Set.diff_union_self]
  exact Set.union_eq_self_of_subset_right (incidenceSet_subset G a)

private def edges_from_set_to_vertex (t : Set V) (a : V) :=
    ((fun u ↦ s(u, a)) '' {x | x ∈ t ∧ G.Adj a x})

private lemma incidenceSet_in_bipartite {s t : Finset V} {a : V}
    (hG : G.IsBipartiteWith (insert a ↑s) ↑t) :
    G.incidenceSet a = edges_from_set_to_vertex (G := G) t a := by
  ext e; cases e; rename_i x y; simp only [mk'_mem_incidenceSet_iff, edges_from_set_to_vertex,
    Set.mem_image, Set.mem_setOf_eq, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk]
  constructor <;> intro h
  · obtain ⟨h, h₀ | h₀⟩ := h
    · subst a; use y; simp only [h, and_true, and_self, or_true]
      have h₀ := hG.mem_of_adj h
      have h₁ := hG.disjoint (x := {x})
      simp at h₁; grind
    · subst a; use x; simp only [h.symm, and_true, and_self, true_or]
      have h₀ := hG.mem_of_adj h
      have h₁ := hG.disjoint (x := {y})
      simp at h₁; grind
  · obtain ⟨w, ⟨h₀, h₁⟩, ⟨h₂, h₃⟩ | ⟨h₂, h₃⟩⟩ := h
    · subst a w; simp [h₁.symm]
    · subst a w; simp [h₁]

private lemma disjoint_edgeSet_decompose (t : Finset V) (a : V) :
    Disjoint (G.deleteIncidenceSet a).edgeSet (edges_from_set_to_vertex (G := G) t a) := by
  rw [Set.disjoint_iff_inter_eq_empty]
  ext e; cases e; rename_i x y;
  simp [deleteIncidenceSet_adj, edges_from_set_to_vertex]
  grind

private lemma ncard_edges_from_set_to_vertex (t : Finset V) (a : V) :
    (edges_from_set_to_vertex (G := G) t a).Finite ∧
    (edges_from_set_to_vertex (G := G) t a).ncard ≤ t.card := by
  have h₁ : {x | x ∈ t ∧ G.Adj a x}.Finite := by
    apply Set.Finite.inter_of_left
    apply Finset.finite_toSet
  have h₂ : (edges_from_set_to_vertex t a).Finite :=
    Set.Finite.image (fun u => s(u, a)) h₁
  have h₅ : (edges_from_set_to_vertex (G := G) t a).ncard ≤
            {x | x ∈ t ∧ G.Adj a x}.ncard :=
    Set.ncard_image_le h₁
  have h₆ : ({x | x ∈ t ∧ G.Adj a x}).ncard ≤ (t : Set V).ncard := by
    apply Set.ncard_inter_le_ncard_left
    exact Set.finite_mem_finset t
  simp only [Set.ncard_coe_finset] at h₆
  refine ⟨h₂, Nat.le_trans h₅ h₆⟩

/-- The upper limit on cardinality of the set of edges in the case of
bipartite graph made from two finsets.
This is proof that the limit is equal to the product of the cardinalities of both finsets. -/
theorem IsBipartiteWith.edgeSet_ncard_le_of_finsets {s t : Finset V}
    (hG : G.IsBipartiteWith ↑s ↑t) :
    G.edgeSet.Finite ∧ G.edgeSet.ncard ≤ s.card * t.card := by
  revert hG G
  induction s using Finset.cons_induction with
  | empty =>
    intros G hG
    have hG₀ : G = ⊥ := by
      ext x y; simp only [bot_adj, iff_false]
      intros hxy; apply hG.mem_of_adj at hxy; simp at hxy
    subst G; simp
  | cons a s h iH =>
    intros G hG
    classical
    simp only [Finset.cons_eq_insert, Finset.coe_insert] at hG
    have hG' : (G.deleteIncidenceSet a).IsBipartiteWith ↑s ↑t :=
      delete_incidence_set_is_bipartite_with_of_is_bipartite_with hG
    obtain ⟨hG'₀, hG'₁⟩ := @iH (G.deleteIncidenceSet a) hG'
    rw [edgeSet_decompose a, incidenceSet_in_bipartite hG]
    simp only [hG'₀, Set.finite_union, Finset.cons_eq_insert, true_and]
    obtain ⟨h₁, h₂⟩ := ncard_edges_from_set_to_vertex (G := G) t a
    refine ⟨h₁, ?_⟩
    rw [Set.ncard_union_eq (hs := hG'₀) (ht := h₁)]
    · simp only [h, not_false_eq_true, Finset.card_insert_of_notMem]
      rw [Nat.succ_mul]
      exact Nat.add_le_add hG'₁ h₂
    · exact disjoint_edgeSet_decompose t a

/-- The upper limit on cardinality of the set of edges, including the cases with infinite sets.
In other words, using `Set.encard`. -/
theorem IsBipartiteWith.encard_edgeSet_le {s t : Set V} (h : G.IsBipartiteWith s t) :
    G.edgeSet.encard ≤ s.encard * t.encard := by
  by_cases hst : s.Finite ∧ t.Finite
  · obtain ⟨hs, ht⟩ := hst
    have inst_s := hs.fintype; have inst_t := ht.fintype
    have hs' : s = ↑(s.toFinset) := by simp
    have ht' : t = ↑(t.toFinset) := by simp
    rw [hs', ht'] at h
    apply IsBipartiteWith.edgeSet_ncard_le_of_finsets at h
    obtain ⟨h₀, h₁⟩ := h
    have h₂ : G.edgeSet.encard = ↑G.edgeSet.ncard := (Set.Finite.cast_ncard_eq h₀).symm
    have h₃ : s.encard = ↑(s.toFinset.card) := Set.encard_eq_coe_toFinset_card s
    have h₄ : t.encard = ↑(t.toFinset.card) := Set.encard_eq_coe_toFinset_card t
    rw [h₂, h₃, h₄]; norm_cast
  · have hst' : s.Infinite ∨ t.Infinite := by tauto
    obtain hs | ht := hst'
    · simp only [hs, Set.Infinite.encard_eq, ge_iff_le]
      by_cases ht₀ : t.encard = 0
      · simp only [ht₀, mul_zero, nonpos_iff_eq_zero, Set.encard_eq_zero, edgeSet_eq_empty]
        ext x y; simp only [bot_adj, iff_false]; intro hxy
        apply h.mem_of_adj at hxy; simp at ht₀; simp [ht₀] at hxy
      · simp [ht₀]
    · simp only [ht, Set.Infinite.encard_eq, ge_iff_le]
      by_cases hs₀ : s.encard = 0
      · simp only [hs₀, zero_mul, nonpos_iff_eq_zero, Set.encard_eq_zero, edgeSet_eq_empty]
        ext x y; simp only [bot_adj, iff_false]; intro hxy
        apply h.mem_of_adj at hxy; simp at hs₀; simp [hs₀] at hxy
      · simp [hs₀]

/-- The upper limit of the cardinality of the edge set of bipartite graph, depending on the
cardinality of vertex set. Four times of edge set cardinality is less or equal to square of
vertex set cardinality. -/
theorem IsBipartite.four_mul_encard_edgeSet_le (h : G.IsBipartite) :
    4 * G.edgeSet.encard ≤ ENat.card V ^ 2 := by
  rw [isBipartite_iff_exists_isBipartiteWith] at h
  obtain ⟨s, t, h⟩ := h
  have hG := IsBipartiteWith.encard_edgeSet_le h
  have h₀ : s.encard + t.encard ≤ ENat.card V := by
    rw [← Set.encard_union_eq h.disjoint]
    exact Set.encard_le_card
  by_cases hv : Finite V
  · have hs : s.Finite := Set.toFinite s
    have ht : t.Finite := Set.toFinite t
    rw [ENat.card_eq_coe_natCard V] at h₀ ⊢
    have hs' : s.encard = ↑(s.ncard) := (Set.Finite.cast_ncard_eq hs).symm
    have ht' : t.encard = ↑(t.ncard) := (Set.Finite.cast_ncard_eq ht).symm
    rw [hs', ht'] at hG h₀
    have h₁ : G.edgeSet.encard = ↑(G.edgeSet.ncard) := by
      rw [Set.Finite.cast_ncard_eq]
      exact Set.toFinite G.edgeSet
    norm_cast at h₀
    have h₂ : (s.ncard + t.ncard) ^ 2 ≤ Nat.card V ^ 2 :=
      Nat.pow_le_pow_left h₀ 2
    rw [h₁] at hG ⊢; norm_cast at *
    have h₃ : 4 * s.ncard * t.ncard ≤ (s.ncard + t.ncard) ^ 2 :=
      four_mul_le_pow_two_add s.ncard t.ncard
    have h₄ : 4 * G.edgeSet.ncard ≤ 4 * s.ncard * t.ncard := by
      rw [mul_assoc]; exact Nat.mul_le_mul_left 4 hG
    exact Nat.le_trans (Nat.le_trans h₄ h₃) h₂
  · simp at hv; simp

private lemma colorable_induce {n} (h : G.Colorable n) (A : Set V) : (G.induce A).Colorable n := by
  simp only [induce, SimpleGraph.comap, Function.Embedding.subtype_apply] at h ⊢
  obtain ⟨colors, property⟩ := h
  use fun a => colors (a.val)
  intros a b hab hab'; simp only [completeGraph_eq_top, top_adj, ne_eq] at property hab
  exact property hab hab'

private lemma edgeSet_encard_of_induce_support :
    (G.induce G.support).edgeSet.encard = G.edgeSet.encard := by
  set f := fun (p : Sym2 ↑G.support) => p.map (fun a => a.val)
  rw [← Function.Injective.encard_image (f := f)]
  · congr; ext x; simp only [Set.mem_image, f]
    constructor <;> intro h
    · obtain ⟨y, h₀, h₁⟩ := h
      cases x with | h x₁ y₁ =>
      cases y with | h x₂ y₂ =>
      simp only [mem_edgeSet, comap_adj, Function.Embedding.subtype_apply, Sym2.map_pair_eq,
        Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at *
      obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := h₁
      · exact h₀
      · exact h₀.symm
    · rw [Sym2.exists]; simp only [mem_edgeSet, comap_adj, Function.Embedding.subtype_apply,
      Sym2.map_pair_eq, Subtype.exists, exists_and_left, exists_prop]
      cases x with | h x y =>
      simp only [mem_edgeSet, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at *
      use x; simp only [true_and]; refine ⟨?_, ?_⟩
      · exact (mem_support G).mpr (by use y)
      · use y; exact ⟨h, (mem_support G).mpr (by use x; exact h.symm), by simp⟩
  · rintro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ h
    simp only [f, Sym2.map_pair_eq, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
      Prod.swap_prod_mk] at h ⊢
    grind

/-- Similar to the ` IsBipartite.four_mul_encard_edgeSet_le` but in this case the upper limit of
four times of edge set cardinality is square of graph's support set cardinality. -/
theorem IsBipartite.four_mul_encard_edgeSet_le_support_encard_sq (h : G.IsBipartite) :
    4 * G.edgeSet.encard ≤ G.support.encard ^ 2 := by
  set G' := G.induce ↑G.support
  have G'_isBipartite : G'.IsBipartite := colorable_induce h _
  have G'_edgeSet_encard : G'.edgeSet.encard = G.edgeSet.encard :=
    edgeSet_encard_of_induce_support
  apply IsBipartite.four_mul_encard_edgeSet_le at G'_isBipartite
  rwa [G'_edgeSet_encard] at G'_isBipartite

end

end SimpleGraph
