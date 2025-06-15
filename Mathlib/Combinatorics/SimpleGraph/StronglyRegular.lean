/-
Copyright (c) 2021 Alena Gusakov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alena Gusakov, Jeremy Tan
-/
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix

/-!
# Strongly regular graphs

## Main definitions

* `G.IsSRGWith n k ℓ μ` (see `SimpleGraph.IsSRGWith`) is a structure for
  a `SimpleGraph` satisfying the following conditions:
  * The cardinality of the vertex set is `n`
  * `G` is a regular graph with degree `k`
  * The number of common neighbors between any two adjacent vertices in `G` is `ℓ`
  * The number of common neighbors between any two nonadjacent vertices in `G` is `μ`

## Main theorems

* `IsSRGWith.compl`: the complement of a strongly regular graph is strongly regular.
* `IsSRGWith.param_eq`: `k * (k - ℓ - 1) = (n - k - 1) * μ` when `0 < n`.
* `IsSRGWith.matrix_eq`: let `A` and `C` be `G`'s and `Gᶜ`'s adjacency matrices respectively and
  `I` be the identity matrix, then `A ^ 2 = k • I + ℓ • A + μ • C`.
-/


open Finset

universe u

namespace SimpleGraph

variable {V : Type u} [Fintype V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A graph is strongly regular with parameters `n k ℓ μ` if
* its vertex set has cardinality `n`
* it is regular with degree `k`
* every pair of adjacent vertices has `ℓ` common neighbors
* every pair of nonadjacent vertices has `μ` common neighbors
-/
structure IsSRGWith (n k ℓ μ : ℕ) : Prop where
  card : Fintype.card V = n
  regular : G.IsRegularOfDegree k
  of_adj : ∀ v w, G.Adj v w → Fintype.card (G.commonNeighbors v w) = ℓ
  of_not_adj : Pairwise fun v w ↦ ¬G.Adj v w → Fintype.card (G.commonNeighbors v w) = μ

variable {G} {n k ℓ μ : ℕ}

/-- Empty graphs are strongly regular. Note that `ℓ` can take any value
for empty graphs, since there are no pairs of adjacent vertices. -/
theorem bot_strongly_regular : (⊥ : SimpleGraph V).IsSRGWith (Fintype.card V) 0 ℓ 0 where
  card := rfl
  regular := bot_degree
  of_adj _ _ h := h.elim
  of_not_adj v w _ := by
    simp only [card_eq_zero, Fintype.card_ofFinset, forall_true_left, not_false_iff, bot_adj]
    ext
    simp [mem_commonNeighbors]

/-- **Conway's 99-graph problem** (from https://oeis.org/A248380/a248380.pdf)
can be reformulated as the existence of a strongly regular graph with params (99, 14, 1, 2).
This is an open problem, and has no known proof of existence. -/
proof_wanted conway_99 : ∃ α : Type*, ∃ (g : SimpleGraph α), IsSRGWith G 99 14 1 2

variable [DecidableEq V]

/-- Complete graphs are strongly regular. Note that `μ` can take any value
for complete graphs, since there are no distinct pairs of non-adjacent vertices. -/
theorem IsSRGWith.top :
    (⊤ : SimpleGraph V).IsSRGWith (Fintype.card V) (Fintype.card V - 1) (Fintype.card V - 2) μ where
  card := rfl
  regular := IsRegularOfDegree.top
  of_adj _ _ := card_commonNeighbors_top
  of_not_adj v w h h' := (h' ((top_adj v w).2 h)).elim

theorem IsSRGWith.card_neighborFinset_union_eq {v w : V} (h : G.IsSRGWith n k ℓ μ) :
    #(G.neighborFinset v ∪ G.neighborFinset w) =
      2 * k - Fintype.card (G.commonNeighbors v w) := by
  apply Nat.add_right_cancel (m := Fintype.card (G.commonNeighbors v w))
  rw [Nat.sub_add_cancel, ← Set.toFinset_card]
  · simp [commonNeighbors, ← neighborFinset_def, Finset.card_union_add_card_inter,
      h.regular.degree_eq, two_mul]
  · apply le_trans (card_commonNeighbors_le_degree_left _ _ _)
    simp [h.regular.degree_eq, two_mul]

/-- Assuming `G` is strongly regular, `2*(k + 1) - m` in `G` is the number of vertices that are
adjacent to either `v` or `w` when `¬G.Adj v w`. So it's the cardinality of
`G.neighborSet v ∪ G.neighborSet w`. -/
theorem IsSRGWith.card_neighborFinset_union_of_not_adj {v w : V} (h : G.IsSRGWith n k ℓ μ)
    (hne : v ≠ w) (ha : ¬G.Adj v w) :
    #(G.neighborFinset v ∪ G.neighborFinset w) = 2 * k - μ := by
  rw [← h.of_not_adj hne ha]
  exact h.card_neighborFinset_union_eq

theorem IsSRGWith.card_neighborFinset_union_of_adj {v w : V} (h : G.IsSRGWith n k ℓ μ)
    (ha : G.Adj v w) : #(G.neighborFinset v ∪ G.neighborFinset w) = 2 * k - ℓ := by
  rw [← h.of_adj v w ha]
  exact h.card_neighborFinset_union_eq

theorem compl_neighborFinset_sdiff_inter_eq {v w : V} :
    (G.neighborFinset v)ᶜ \ {v} ∩ ((G.neighborFinset w)ᶜ \ {w}) =
      ((G.neighborFinset v)ᶜ ∩ (G.neighborFinset w)ᶜ) \ ({w} ∪ {v}) := by
  ext
  rw [← not_iff_not]
  simp [imp_iff_not_or, or_assoc, or_comm, or_left_comm]

theorem sdiff_compl_neighborFinset_inter_eq {v w : V} (h : G.Adj v w) :
    ((G.neighborFinset v)ᶜ ∩ (G.neighborFinset w)ᶜ) \ ({w} ∪ {v}) =
      (G.neighborFinset v)ᶜ ∩ (G.neighborFinset w)ᶜ := by
  ext
  simp only [and_imp, mem_union, mem_sdiff, mem_compl, and_iff_left_iff_imp, mem_neighborFinset,
    mem_inter, mem_singleton]
  rintro hnv hnw (rfl | rfl)
  · exact hnv h
  · apply hnw
    rwa [adj_comm]

theorem IsSRGWith.compl_is_regular (h : G.IsSRGWith n k ℓ μ) :
    Gᶜ.IsRegularOfDegree (n - k - 1) := by
  rw [← h.card, Nat.sub_sub, add_comm, ← Nat.sub_sub]
  exact h.regular.compl

theorem IsSRGWith.card_commonNeighbors_eq_of_adj_compl (h : G.IsSRGWith n k ℓ μ) {v w : V}
    (ha : Gᶜ.Adj v w) : Fintype.card (Gᶜ.commonNeighbors v w) = n - (2 * k - μ) - 2 := by
  simp only [← Set.toFinset_card, commonNeighbors, Set.toFinset_inter, neighborSet_compl,
    Set.toFinset_diff, Set.toFinset_singleton, Set.toFinset_compl, ← neighborFinset_def]
  simp_rw [compl_neighborFinset_sdiff_inter_eq]
  have hne : v ≠ w := ne_of_adj _ ha
  rw [compl_adj] at ha
  rw [card_sdiff, ← insert_eq, card_insert_of_notMem, card_singleton, ← Finset.compl_union]
  · rw [card_compl, h.card_neighborFinset_union_of_not_adj hne ha.2, ← h.card]
  · simp only [hne.symm, not_false_iff, mem_singleton]
  · intro u
    simp only [mem_union, mem_compl, mem_neighborFinset, mem_inter, mem_singleton]
    rintro (rfl | rfl) <;> simpa [adj_comm] using ha.2

theorem IsSRGWith.card_commonNeighbors_eq_of_not_adj_compl (h : G.IsSRGWith n k ℓ μ) {v w : V}
    (hn : v ≠ w) (hna : ¬Gᶜ.Adj v w) :
    Fintype.card (Gᶜ.commonNeighbors v w) = n - (2 * k - ℓ) := by
  simp only [← Set.toFinset_card, commonNeighbors, Set.toFinset_inter, neighborSet_compl,
    Set.toFinset_diff, Set.toFinset_singleton, Set.toFinset_compl, ← neighborFinset_def]
  simp only [not_and, Classical.not_not, compl_adj] at hna
  have h2' := hna hn
  simp_rw [compl_neighborFinset_sdiff_inter_eq, sdiff_compl_neighborFinset_inter_eq h2']
  rwa [← Finset.compl_union, card_compl, h.card_neighborFinset_union_of_adj, ← h.card]

/-- The complement of a strongly regular graph is strongly regular. -/
theorem IsSRGWith.compl (h : G.IsSRGWith n k ℓ μ) :
    Gᶜ.IsSRGWith n (n - k - 1) (n - (2 * k - μ) - 2) (n - (2 * k - ℓ)) where
  card := h.card
  regular := h.compl_is_regular
  of_adj _ _ := h.card_commonNeighbors_eq_of_adj_compl
  of_not_adj _ _ := h.card_commonNeighbors_eq_of_not_adj_compl

/-- The parameters of a strongly regular graph with at least one vertex satisfy
`k * (k - ℓ - 1) = (n - k - 1) * μ`. -/
theorem IsSRGWith.param_eq
    {V : Type u} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : G.IsSRGWith n k ℓ μ) (hn : 0 < n) :
    k * (k - ℓ - 1) = (n - k - 1) * μ := by
  letI := Classical.decEq V
  rw [← h.card, Fintype.card_pos_iff] at hn
  obtain ⟨v⟩ := hn
  convert card_mul_eq_card_mul G.Adj (s := G.neighborFinset v) (t := Gᶜ.neighborFinset v) _ _
  · simp [h.regular v]
  · simp [h.compl.regular v]
  · intro w hw
    rw [mem_neighborFinset] at hw
    simp_rw [bipartiteAbove, ← mem_neighborFinset, filter_mem_eq_inter]
    have s : {v} ⊆ G.neighborFinset w \ G.neighborFinset v := by
      rw [singleton_subset_iff, mem_sdiff, mem_neighborFinset]
      exact ⟨hw.symm, G.notMem_neighborFinset_self v⟩
    rw [inter_comm, neighborFinset_compl, ← inter_sdiff_assoc, ← sdiff_eq_inter_compl, card_sdiff s,
      card_singleton, ← sdiff_inter_self_left, card_sdiff inter_subset_left]
    congr
    · simp [h.regular w]
    · simp_rw [inter_comm, neighborFinset_def, ← Set.toFinset_inter, ← h.of_adj v w hw,
        ← Set.toFinset_card]
      congr!
  · intro w hw
    simp_rw [neighborFinset_compl, mem_sdiff, mem_compl, mem_singleton, mem_neighborFinset,
      ← Ne.eq_def] at hw
    simp_rw [bipartiteBelow, adj_comm, ← mem_neighborFinset, filter_mem_eq_inter,
      neighborFinset_def, ← Set.toFinset_inter, ← h.of_not_adj hw.2.symm hw.1,
      ← Set.toFinset_card]
    congr!

/-- Let `A` and `C` be the adjacency matrices of a strongly regular graph with parameters `n k ℓ μ`
and its complement respectively and `I` be the identity matrix,
then `A ^ 2 = k • I + ℓ • A + μ • C`. `C` is equivalent to the expression `J - I - A`
more often found in the literature, where `J` is the all-ones matrix. -/
theorem IsSRGWith.matrix_eq {α : Type*} [Semiring α] (h : G.IsSRGWith n k ℓ μ) :
    G.adjMatrix α ^ 2 = k • (1 : Matrix V V α) + ℓ • G.adjMatrix α + μ • Gᶜ.adjMatrix α := by
  ext v w
  simp only [adjMatrix_pow_apply_eq_card_walk, Set.coe_setOf, Matrix.add_apply, Matrix.smul_apply,
    adjMatrix_apply, compl_adj]
  rw [Fintype.card_congr (G.walkLengthTwoEquivCommonNeighbors v w)]
  obtain rfl | hn := eq_or_ne v w
  · rw [← Set.toFinset_card]
    simp [commonNeighbors, ← neighborFinset_def, h.regular v]
  · simp only [Matrix.one_apply_ne' hn.symm, ne_eq, hn]
    by_cases ha : G.Adj v w <;>
      simp only [ha, ite_true, ite_false, add_zero, zero_add, nsmul_eq_mul, smul_zero, mul_one,
        not_true_eq_false, not_false_eq_true, and_false, and_self]
    · rw [h.of_adj v w ha]
    · rw [h.of_not_adj hn ha]

end SimpleGraph
