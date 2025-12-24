/-
Copyright (c) 2025 Mitchell Horner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Horner, Sun Yue, Nick Adfor, Aristotle
-/
module

public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Combinatorics.SimpleGraph.Coloring
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Tactic.Cases

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

## Odd Cycle Theorem (A Solution to TODO)

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

section OddCycleTheorem

lemma even_length_iff_same_color
    {c : G.Coloring (Fin 2)}
    {u v : V} (p : G.Walk u v) :
    Even p.length ↔ c u = c v := by
  induction p with
  | nil =>
    -- Base case: length 0 is even, c u = c u is true
    simp
  | cons h_adj p_tail ih =>
    -- Inductive step
    -- Goal: Even (cons ...).length ↔ c u = c w
    have h_first_step_diff := c.valid h_adj
    rw [SimpleGraph.Walk.length_cons]
    rw [Nat.even_add_one] -- 1 + x is even <-> x is odd
    -- Using induction hypothesis ih: Even p_tail.length ↔ c v = c w
    rw [ih]
    -- Now the goal becomes: ¬(c v = c w) ↔ c u = c w
    constructor
    · -- Direction 1: (c next ≠ c end) -> (c start = c end)
      intro h_next_ne_end
      have h_cases : c u = 0 ∨ c u = 1 := by
        match c u with
        | 0 => left; rfl
        | 1 => right; rfl
      cases h_cases
      · -- Case 1: c u = 0
        simp_all
        omega
      · -- Case 2: c u = 1
        simp_all
        omega
    · -- Direction 2: (c start = c end) -> (c next ≠ c end)
      intro h_start_eq_end
      -- Given: start ≠ next
      -- Replacing start with end, we get end ≠ next
      rw [h_start_eq_end] at h_first_step_diff
      exact h_first_step_diff.symm

/-- Sufficient lemma. -/
lemma bipartite_implies_even_cycles (h : G.IsBipartite) :
    ∀ (v : V) (c : G.Walk v v), c.IsCycle → Even c.length := by
  -- 1. Since it's a bipartite graph, there exists a 2-coloring scheme (color : V -> Bool)
  rcases h with ⟨color⟩
  -- 2. Analyze any cycle c
  intro v c hc
  -- 3. Use Walk property: In a bipartite graph, if a path has same start and end color,
  --    then the path length must be even.
  --    A cycle starts and ends at the same point v, so colors are obviously the same.
  have h_color_eq : color v = color v := rfl
  -- 4. Call the lemma about bipartite path parity in Mathlib
  -- (SimpleGraph.Coloring.valid_walk_length_even_iff)
  rw [even_length_iff_same_color]
  exact color

namespace SimpleGraph.walk

/-- Helper lemma 1: The prefix of a shortest path is also a shortest path. -/
lemma dist_eq_length_takeUntil {u v x : V} (p : G.Walk u v) (hp : p.IsPath)
    (hp_len : p.length = G.dist u v) (hx : x ∈ p.support) :
    (p.takeUntil x hx).length = G.dist u x := by
  -- Strategy: Prove takeUntil yields a path, and length ≤ dist
  -- Since dist ≤ length of any walk, they are equal
  let p_to_x := p.takeUntil x hx
  -- p_to_x is a path
  have hp_to_x : p_to_x.IsPath := by
    have : (p.takeUntil x hx).append (p.dropUntil x hx) = p := p.take_spec hx
    exact hp.takeUntil _
  -- p_to_x.length ≤ p.length
  have h_le : p_to_x.length ≤ p.length := SimpleGraph.Walk.length_takeUntil_le p hx
  have h_triangle : G.dist u v ≤ G.dist u x + G.dist x v := by
    by_cases h : G.Reachable u x ∧ G.Reachable x v
    · obtain ⟨q, hq⟩ : ∃ q : G.Walk u x, q.length = G.dist u x := by
        have := h.1
        exact Reachable.exists_walk_length_eq_dist this
      obtain ⟨r, hr⟩ : ∃ r : G.Walk x v, r.length = G.dist x v := by
        obtain ⟨r, hr⟩ : ∃ r : G.Walk x v, r.length = G.dist x v := by
          have h_reachable : G.Reachable x v := h.right
          exact Reachable.exists_walk_length_eq_dist h_reachable
        use r
      exact SimpleGraph.dist_le (q.append r) |> le_trans <| by simp +decide [hq, hr]
    · cases hp_to_x
      simp_all +decide [SimpleGraph.Reachable]
      contrapose! h
      exact ⟨p_to_x, ⟨p.dropUntil x hx⟩⟩
  have h_dist_xv_le : G.dist x v ≤ (p.dropUntil x hx).length := SimpleGraph.dist_le (p.dropUntil x hx)
  have h_eq_parts : p.length = p_to_x.length + (p.dropUntil x hx).length := by
    have := congr_arg Walk.length (p.take_spec hx)
    -- The length of the appended walk is the sum of the lengths of the two parts.
    rw [← this]
    -- The length of the appended walk is the sum of the lengths of the two parts by definition.
    apply SimpleGraph.Walk.length_append
  have h_upper : p_to_x.length ≤ G.dist u x := by
    rw [hp_len] at h_eq_parts
    have := calc G.dist u v
      _ ≤ G.dist u x + G.dist x v := h_triangle
      _ ≤ G.dist u x + (p.dropUntil x hx).length := Nat.add_le_add_left h_dist_xv_le _
    omega
  refine' le_antisymm h_upper _
  exact dist_le (p.takeUntil x hx)

/-- Helper lemma 2: Length of the suffix of a shortest path. -/
lemma length_dropUntil_eq_dist_sub {u v x : V} (p : G.Walk u v) (hp : p.IsPath)
    (hp_len : p.length = G.dist u v) (hx : x ∈ p.support) :
    (p.dropUntil x hx).length = G.dist u v - G.dist u x := by
  have h1 := congr_arg Walk.length (p.take_spec hx)
  have h4 : (p.takeUntil x hx).length = G.dist u x := by
    rw [SimpleGraph.Walk.dist_eq_length_takeUntil]
    · assumption
    · exact hp_len
  rw [← h4, ← hp_len, ← h1, SimpleGraph.Walk.length_append]
  aesop

lemma two_colorable_iff_forall_loop_even {α : Type*} {G : SimpleGraph α} :
    G.Colorable 2 ↔ ∀ u, ∀ (w : G.Walk u u), Even w.length := by
    exact SimpleGraph.two_colorable_iff_forall_loop_even

lemma bypass_eq_nil_of_closed {V : Type*} [DecidableEq V] {G : SimpleGraph V} {u : V} (w : G.Walk u u) :
    w.bypass = SimpleGraph.Walk.nil := by
      have h_nil : ∀ {u : V} {p : G.Walk u u}, p.IsPath → p = SimpleGraph.Walk.nil := by
        aesop
      exact h_nil (SimpleGraph.Walk.bypass_isPath _)

lemma even_cycle_length_of_path
    (h_cycles : ∀ (v : V) (c : G.Walk v v), c.IsCycle → Even c.length)
    {u v : V} (q : G.Walk v u) (hq : q.IsPath) (ha : G.Adj u v) :
    Even (SimpleGraph.Walk.cons ha q).length := by
      by_cases hq' : q.length = 1 <;> simp_all +decide [parity_simps]
      have h_cycle : SimpleGraph.Walk.IsCycle (SimpleGraph.Walk.cons ha q) := by
        simp_all +decide [SimpleGraph.Walk.isCycle_def]
        refine' ⟨⟨_, _⟩, _⟩
        · exact hq.isTrail
        · intro h
          cases q <;> simp_all +decide [SimpleGraph.Walk.edges]
          rcases h with ((⟨rfl, rfl⟩ | rfl) | ⟨a, ha, ha'⟩) <;> simp_all +decide [SimpleGraph.Walk.mem_support_iff]
          have := SimpleGraph.Walk.dart_fst_mem_support_of_mem_darts _ ha; simp_all +decide [SimpleGraph.Walk.mem_support_iff]
          cases a
          simp_all +decide
          cases ha' <;> simp_all +decide
          cases this <;> simp_all +decide
          · aesop
          · have := SimpleGraph.Walk.dart_snd_mem_support_of_mem_darts _ ha; simp_all +decide [SimpleGraph.Walk.mem_support_iff]
        · exact hq.support_nodup
      have := h_cycles u (SimpleGraph.Walk.cons ha q) h_cycle; simp_all +decide [parity_simps]

lemma even_length_iff_even_bypass_length
    (h : ∀ (v : V) (c : G.Walk v v), c.IsCycle → Even c.length)
    {u v : V} (p : G.Walk u v) :
    Even p.length ↔ Even p.bypass.length := by
      induction' p with u v pᵥ _ ih <;> simp_all +decide
      · exact even_iff_two_dvd.mpr ⟨0, rfl⟩
      · by_cases h : v ∈ (‹G.Walk pᵥ _›.bypass).support <;> simp_all +decide [SimpleGraph.Walk.bypass]
        · -- By Lemma 2, the length of the bypass of a path is equal to the length of the path minus the length of the prefix.
          have h_bypass : (‹G.Walk pᵥ _›.bypass.length) = (‹G.Walk pᵥ _›.bypass.takeUntil v h).length + (‹G.Walk pᵥ _›.bypass.dropUntil v h).length := by
            rw [← SimpleGraph.Walk.length_append, SimpleGraph.Walk.take_spec _ _]
          -- By Lemma 2, the length of the bypass of a path is equal to the length of the path minus the length of the prefix, and the length of the prefix is even.
          have h_prefix_even : Even ((‹G.Walk pᵥ _›.bypass.takeUntil v h).length + 1) := by
            have h_prefix_even : Even ((SimpleGraph.Walk.cons ih (‹G.Walk pᵥ _›.bypass.takeUntil v h)).length) := by
              apply even_cycle_length_of_path
              · assumption
              · exact SimpleGraph.Walk.IsPath.takeUntil (SimpleGraph.Walk.bypass_isPath _) _
            simpa [add_comm] using h_prefix_even
          simp_all +decide [parity_simps]
          by_cases h : Even (‹G.Walk pᵥ _›.bypass.dropUntil v h).length <;> simp_all +decide [Nat.even_iff, Nat.odd_iff]
        · grind

theorem bipartite_iff_all_cycles_even :
  G.IsBipartite ↔ ∀ (v : V) (c : G.Walk v v), c.IsCycle → Even c.length := by
  constructor
  · -- Forward direction: G is bipartite → all cycles have even length
    intro h_bip
    exact bipartite_implies_even_cycles G h_bip
  · -- Assume all cycles have even length. We need to show that the graph is bipartite.
    intro h
    have h_colorable : G.Colorable 2 := by
      -- By the lemma, this implies that G is colorable with 2 colors. We can use the lemma `two_colorable_iff_forall_loop_even` which states that a graph is 2-colorable if and only if every closed walk has even length.
      apply (two_colorable_iff_forall_loop_even).mpr
      intro u w
      -- By `even_length_iff_even_bypass_length`, `Even w.length ↔ Even w.bypass.length`.
      have h_even_bypass : Even w.length ↔ Even w.bypass.length := by
        apply even_length_iff_even_bypass_length
        assumption
      rw [h_even_bypass]
      rw [bypass_eq_nil_of_closed]
      aesop
    exact Colorable.mono_left (fun ⦃v w⦄ a => a) h_colorable

end SimpleGraph
