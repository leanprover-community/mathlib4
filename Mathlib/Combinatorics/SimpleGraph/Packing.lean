/-
Copyright (c) 2026 Thiago Campos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thiago Campos
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Combinatorics.SimpleGraph.Copy

/-!
# Packing of graphs

Two simple graphs `G` and `H` *pack* if there is an injection from the vertices of `G` to the
vertices of `H` sending edges of `G` to non-edges of `H`, that is, if `G` and `H` can be placed
edge-disjointly in the complete graph on the vertices of `H`. In terms of `SimpleGraph.Copy`, this
is the statement `G ⊑ Hᶜ`.

## Main statements

* `SimpleGraph.isContained_compl_of_two_mul_maxDegree_mul_lt`: the **Sauer–Spencer theorem**. If
  `G` has at most as many vertices as `H` and `2 * G.maxDegree * H.maxDegree` is less than the
  number of vertices of `H`, then `G` and `H` pack.

## Implementation notes

We pick an embedding `f` of the vertices of `G` into those of `H` for which the subgraph
`G ⊓ H.comap f` of edges of `G` sent to edges of `H` is minimal. If this subgraph had an edge `uv`,
then by the degree condition there would be a vertex `w` such that composing `f` with the
transposition of `f u` and `w` removes `uv` from this subgraph without adding any new edge,
contradicting minimality.

## References

* N. Sauer and J. Spencer, *Edge disjoint placement of graphs*,
  J. Combin. Theory Ser. B 25 (1978), 295–302.
-/

public section

open Finset Function

namespace SimpleGraph

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

/-- Suppose that `f` sends the edge `uv` of `G` to an edge of `H`, and let `w ≠ f v` be a vertex
which is not `H`-adjacent to the image of any `G`-neighbor of `u`, and which is not the image of
any `G`-neighbor of a vertex sent to an `H`-neighbor of `f u`. Then swapping `f u` and `w`
removes `uv` from `G ⊓ H.comap f` without adding any new edge. -/
private lemma inf_comap_swap_lt [DecidableEq W] {f : V ↪ W} {u v : V} {w : W}
    (huv : G.Adj u v) (hf : H.Adj (f u) (f v)) (hwv : w ≠ f v)
    (hw₁ : ∀ y, G.Adj u y → ¬H.Adj (f y) w)
    (hw₂ : ∀ y, H.Adj (f u) (f y) → ∀ x, G.Adj y x → f x ≠ w) :
    G ⊓ H.comap (f.trans (Equiv.swap (f u) w).toEmbedding) < G ⊓ H.comap f := by
  refine lt_of_le_not_ge (fun x y ⟨hxy, hH⟩ ↦ ⟨hxy, ?_⟩) fun hle ↦ hw₁ v huv ?_
  · -- Case analysis on whether `x` and `y` are sent to `f u` or `w`.
    simp only [comap_adj, Embedding.trans_apply, Equiv.coe_toEmbedding, Equiv.swap_apply_def,
      EmbeddingLike.apply_eq_iff_eq] at hH ⊢
    grind [Adj.symm]
  · simpa [Equiv.swap_apply_of_ne_of_ne (f.injective.ne huv.ne') hwv.symm, adj_comm] using
      (hle ⟨huv, hf⟩).2

variable [Fintype V] [Fintype W] [DecidableRel G.Adj] [DecidableRel H.Adj]

/-- If `2 * G.maxDegree * H.maxDegree < Fintype.card W` and `f` sends some edge of `G` to an edge
of `H`, then some embedding `g` satisfies `G ⊓ H.comap g < G ⊓ H.comap f`. -/
private lemma exists_inf_comap_lt (h : 2 * G.maxDegree * H.maxDegree < Fintype.card W)
    {f : V ↪ W} {u v : V} (huv : G.Adj u v) (hf : H.Adj (f u) (f v)) :
    ∃ g : V ↪ W, G ⊓ H.comap g < G ⊓ H.comap f := by
  classical
  -- Apart from `f v`, these are the vertices with which `f u` cannot be swapped.
  let B₁ := (G.neighborFinset u).biUnion fun y ↦ H.neighborFinset (f y)
  let B₂ := ((H.comap f).neighborFinset u).biUnion fun y ↦ (G.neighborFinset y).map f
  have h₁ : #B₁ ≤ G.maxDegree * H.maxDegree :=
    (card_biUnion_le_card_mul _ _ _ fun y _ ↦ H.degree_le_maxDegree (f y)).trans <|
      Nat.mul_le_mul_right _ (G.degree_le_maxDegree u)
  have h₂ : #B₂ ≤ H.maxDegree * G.maxDegree := by
    refine (card_biUnion_le_card_mul _ _ _ fun y _ ↦ ?_).trans (Nat.mul_le_mul_right _ ?_)
    · exact (card_map f).trans_le (G.degree_le_maxDegree y)
    · exact ((Embedding.comap f H).toCopy.degree_le u).trans (H.degree_le_maxDegree _)
  have hu : f u ∈ B₁ ∩ B₂ := by
    simp only [B₁, B₂, mem_inter, mem_biUnion, mem_map, mem_neighborFinset, comap_adj]
    exact ⟨⟨v, huv, hf.symm⟩, v, hf, u, huv.symm, rfl⟩
  have hB : #(insert (f v) (B₁ ∪ B₂)) < #(univ : Finset W) := by
    grind [card_univ, card_insert_le, card_union_add_card_inter, card_pos]
  obtain ⟨w, -, hw⟩ := exists_mem_notMem_of_card_lt_card hB
  simp only [B₁, B₂, mem_insert, mem_union, mem_biUnion, mem_map, mem_neighborFinset, comap_adj,
    not_or, not_exists, not_and] at hw
  obtain ⟨hwv, hw₁, hw₂⟩ := hw
  exact ⟨_, inf_comap_swap_lt huv hf hwv hw₁ hw₂⟩

/-- The **Sauer–Spencer theorem**: if `G` has at most as many vertices as `H` and
`2 * G.maxDegree * H.maxDegree` is less than the number of vertices of `H`, then `G` and `H` pack,
that is, `G` is contained in the complement of `H`. -/
theorem isContained_compl_of_two_mul_maxDegree_mul_lt
    (hcard : Fintype.card V ≤ Fintype.card W)
    (h : 2 * G.maxDegree * H.maxDegree < Fintype.card W) : G ⊑ Hᶜ := by
  have := Embedding.nonempty_of_card_le hcard
  -- Pick an embedding sending a minimal set of edges of `G` to edges of `H`.
  obtain ⟨f, hmin⟩ : ∃ f : V ↪ W, ∀ g : V ↪ W, ¬G ⊓ H.comap g < G ⊓ H.comap f :=
    ⟨_, not_lt_argmin fun f : V ↪ W ↦ G ⊓ H.comap f⟩
  refine ⟨⟨⟨f, fun huv ↦ ⟨f.injective.ne huv.ne, fun hH ↦ ?_⟩⟩, f.injective⟩⟩
  exact (exists_inf_comap_lt h huv hH).elim hmin

end SimpleGraph
