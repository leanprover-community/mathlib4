/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import Mathlib.Algebra.GroupPower.Order
import Mathlib.Algebra.Order.Field.Defs
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity

#align_import combinatorics.SimpleGraph.triangle.basic from "leanprover-community/mathlib"@"3365b20c2ffa7c35e47e5209b89ba9abdddf3ffe"

/-!
# Triangles in graphs

A *triangle* in a simple graph is a `3`-clique, namely a Set of three vertices that are
pairwise adjacent.

This module defines and proves properties about triangles in simple graphs.

## Main declarations

* `SimpleGraph.FarFromTriangleFree`: Predicate for a graph such that one must remove a lot of edges
  from it for it to become triangle-free. This is the crux of the Triangle Removal Lemma.

## TODO

* Generalise `FarFromTriangleFree` to other graphs, to state and prove the Graph Removal Lemma.
-/

open Finset Nat
open Fintype (card)

namespace SimpleGraph

variable {α β 𝕜 : Type*} [LinearOrderedField 𝕜] {G H : SimpleGraph α} {ε δ : 𝕜} {n : ℕ}
  {s : Finset α}

section LocallyLinear

/-- A graph has edge-disjoint triangles if each edge belongs to at most one triangle. -/
def EdgeDisjointTriangles (G : SimpleGraph α) : Prop :=
  (G.cliqueSet 3).Pairwise fun x y ↦ (x ∩ y : Set α).Subsingleton

/-- A graph is locally linear if each edge belongs to exactly one triangle. -/
def LocallyLinear (G : SimpleGraph α) : Prop :=
  G.EdgeDisjointTriangles ∧ ∀ ⦃x y⦄, G.Adj x y → ∃ s, G.IsNClique 3 s ∧ x ∈ s ∧ y ∈ s

protected lemma LocallyLinear.edgeDisjointTriangles : G.LocallyLinear → G.EdgeDisjointTriangles :=
  And.left

nonrec lemma EdgeDisjointTriangles.mono (h : G ≤ H) (hH : H.EdgeDisjointTriangles) :
    G.EdgeDisjointTriangles := hH.mono $ cliqueSet_mono h

@[simp] lemma edgeDisjointTriangles_bot : (⊥ : SimpleGraph α).EdgeDisjointTriangles := by
  simp [EdgeDisjointTriangles]

@[simp] lemma locallyLinear_bot : (⊥ : SimpleGraph α).LocallyLinear := by simp [LocallyLinear]

lemma EdgeDisjointTriangles.map (f : α ↪ β) (hG : G.EdgeDisjointTriangles) :
    (G.map f).EdgeDisjointTriangles := by
  rw [EdgeDisjointTriangles, cliqueSet_map (by norm_num : 3 ≠ 1),
    ((Finset.map_injective f).injOn _).pairwise_image]
  classical
  rintro s hs t ht hst
  dsimp [Function.onFun]
  rw [← coe_inter, ← map_inter, coe_map, coe_inter]
  exact (hG hs ht hst).image _

lemma LocallyLinear.map (f : α ↪ β) (hG : G.LocallyLinear) : (G.map f).LocallyLinear := by
  refine ⟨hG.1.map _, ?_⟩
  rintro _ _ ⟨a, b, h, rfl, rfl⟩
  obtain ⟨s, hs, ha, hb⟩ := hG.2 h
  exact ⟨s.map f, hs.map, mem_map_of_mem _ ha, mem_map_of_mem _ hb⟩

@[simp] lemma locallyLinear_comap {G : SimpleGraph β} {e : α ≃ β} :
    (G.comap e).LocallyLinear ↔ G.LocallyLinear := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · rw [← comap_map_eq e.symm.toEmbedding G, comap_symm, map_symm]
    exact h.map _
  · rw [← Equiv.coe_toEmbedding, ← map_symm]
    exact LocallyLinear.map _

variable [DecidableEq α]

lemma edgeDisjointTriangles_iff_mem_sym2_subsingleton :
    G.EdgeDisjointTriangles ↔
      ∀ ⦃e : Sym2 α⦄, ¬ e.IsDiag → {s ∈ G.cliqueSet 3 | e ∈ (s : Finset α).sym2}.Subsingleton := by
  have (a b) (hab : a ≠ b) : {s ∈ (G.cliqueSet 3 : Set (Finset α)) | s(a, b) ∈ (s : Finset α).sym2}
    = {s | G.Adj a b ∧ ∃ c, G.Adj a c ∧ G.Adj b c ∧ s = {a, b, c}} := by
    ext s
    simp only [mem_sym2_iff, Sym2.mem_iff, forall_eq_or_imp, forall_eq, Set.sep_and,
      Set.mem_inter_iff, Set.mem_sep_iff, mem_cliqueSet_iff, Set.mem_setOf_eq,
      and_and_and_comm (b := _ ∈ _), and_self, is3Clique_iff]
    constructor
    · rintro ⟨⟨c, d, e, hcd, hce, hde, rfl⟩, hab⟩
      simp only [mem_insert, mem_singleton] at hab
      obtain ⟨rfl | rfl | rfl, rfl | rfl | rfl⟩ := hab
      any_goals
        simp only [*, adj_comm, true_and, Ne, eq_self_iff_true, not_true] at *
      any_goals
        first
        | exact ⟨c, by aesop⟩
        | exact ⟨d, by aesop⟩
        | exact ⟨e, by aesop⟩
        | simp only [*, adj_comm, true_and, Ne, eq_self_iff_true, not_true] at *
          exact ⟨c, by aesop⟩
        | simp only [*, adj_comm, true_and, Ne, eq_self_iff_true, not_true] at *
          exact ⟨d, by aesop⟩
        | simp only [*, adj_comm, true_and, Ne, eq_self_iff_true, not_true] at *
          exact ⟨e, by aesop⟩
    · rintro ⟨hab, c, hac, hbc, rfl⟩
      refine ⟨⟨a, b, c, ?_⟩, ?_⟩ <;> simp [*]
  constructor
  · rw [Sym2.forall]
    rintro hG a b hab
    simp only [Sym2.isDiag_iff_proj_eq] at hab
    rw [this _ _ (Sym2.mk_isDiag_iff.not.2 hab)]
    rintro _ ⟨hab, c, hac, hbc, rfl⟩ _ ⟨-, d, had, hbd, rfl⟩
    refine hG.eq ?_ ?_ (Set.Nontrivial.not_subsingleton ⟨a, ?_, b, ?_, hab.ne⟩) <;>
      simp [is3Clique_triple_iff, *]
  · simp only [EdgeDisjointTriangles, is3Clique_iff, Set.Pairwise, mem_cliqueSet_iff, Ne,
      forall_exists_index, and_imp, ← Set.not_nontrivial_iff (s := _ ∩ _), not_imp_not,
      Set.Nontrivial, Set.mem_inter_iff, mem_coe]
    rintro hG _ a b c hab hac hbc rfl _ d e f hde hdf hef rfl g hg₁ hg₂ h hh₁ hh₂ hgh
    save
    refine hG (Sym2.mk_isDiag_iff.not.2 hgh) ⟨⟨a, b, c, ?_⟩, by simpa using And.intro hg₁ hh₁⟩
      ⟨⟨d, e, f, ?_⟩, by simpa using And.intro hg₂ hh₂⟩ <;> simp [is3Clique_triple_iff, *]

alias ⟨EdgeDisjointTriangles.mem_sym2_subsingleton, _⟩ :=
  edgeDisjointTriangles_iff_mem_sym2_subsingleton

variable [Fintype α] [DecidableRel G.Adj]

instance EdgeDisjointTriangles.instDecidable : Decidable G.EdgeDisjointTriangles :=
  decidable_of_iff ((G.cliqueFinset 3 : Set (Finset α)).Pairwise fun x y ↦ ((x ∩ y).card ≤ 1)) $ by
    simp only [coe_cliqueFinset, EdgeDisjointTriangles, Finset.card_le_one, ← coe_inter]; rfl

instance LocallyLinear.instDecidable : Decidable G.LocallyLinear := And.decidable

lemma EdgeDisjointTriangles.card_edgeFinset_le (hG : G.EdgeDisjointTriangles) :
    3 * (G.cliqueFinset 3).card ≤ G.edgeFinset.card := by
  rw [mul_comm, ← mul_one G.edgeFinset.card]
  refine card_mul_le_card_mul (fun s e ↦ e ∈ s.sym2) ?_ (fun e he ↦ ?_)
  · simp only [is3Clique_iff, mem_cliqueFinset_iff, mem_sym2_iff, forall_exists_index, and_imp]
    rintro _ a b c hab hac hbc rfl
    have : Finset.card ({s(a, b), s(a, c), s(b, c)} : Finset (Sym2 α)) = 3 := by
      refine card_eq_three.2 ⟨_, _, _, ?_, ?_, ?_, rfl⟩ <;> simp [hab.ne, hac.ne, hbc.ne]
    rw [← this]
    refine card_mono ?_
    simp [insert_subset, *]
  · simpa only [card_le_one, mem_bipartiteBelow, and_imp, Set.Subsingleton, Set.mem_setOf_eq,
      mem_cliqueFinset_iff, mem_cliqueSet_iff]
      using hG.mem_sym2_subsingleton (G.not_isDiag_of_mem_edgeSet $ mem_edgeFinset.1 he)

lemma LocallyLinear.card_edgeFinset (hG : G.LocallyLinear) :
    G.edgeFinset.card = 3 * (G.cliqueFinset 3).card := by
  refine hG.edgeDisjointTriangles.card_edgeFinset_le.antisymm' ?_
  rw [← mul_comm, ← mul_one (Finset.card _)]
  refine card_mul_le_card_mul (fun e s ↦ e ∈ s.sym2) ?_ ?_
  · simpa [Sym2.forall, Nat.one_le_iff_ne_zero, -card_eq_zero, card_ne_zero, Finset.Nonempty]
      using hG.2
  simp only [mem_cliqueFinset_iff, is3Clique_iff, forall_exists_index, and_imp]
  rintro _ a b c hab hac hbc rfl
  calc
    _ ≤ ({s(a, b), s(a, c), s(b, c)} : Finset _).card := card_le_card ?_
    _ ≤ 3 := (card_insert_le _ _).trans (succ_le_succ $ (card_insert_le _ _).trans_eq $ by
      rw [card_singleton])
  simp only [subset_iff, Sym2.forall, mem_sym2_iff, le_eq_subset, mem_bipartiteBelow, mem_insert,
    mem_edgeFinset, mem_singleton, and_imp, mem_edgeSet, Sym2.mem_iff, forall_eq_or_imp,
    forall_eq, Quotient.eq, Sym2.rel_iff]
  rintro d e hde (rfl | rfl | rfl) (rfl | rfl | rfl) <;> simp [*] at *

end LocallyLinear

variable (G ε)
variable [Fintype α] [DecidableEq α] [DecidableRel G.Adj] [DecidableRel H.Adj]

/-- A simple graph is *`ε`-far from triangle-free* if one must remove at least
`ε * (card α) ^ 2` edges to make it triangle-free. -/
def FarFromTriangleFree : Prop := G.DeleteFar (fun H ↦ H.CliqueFree 3) <| ε * (card α ^ 2 : ℕ)
#align simple_graph.far_from_triangle_free SimpleGraph.FarFromTriangleFree

variable {G ε}

theorem farFromTriangleFree_iff :
    G.FarFromTriangleFree ε ↔ ∀ ⦃H : SimpleGraph α⦄, [DecidableRel H.Adj] → H ≤ G → H.CliqueFree 3 →
      ε * (card α ^ 2 : ℕ) ≤ G.edgeFinset.card - H.edgeFinset.card := deleteFar_iff
#align simple_graph.far_from_triangle_free_iff SimpleGraph.farFromTriangleFree_iff

alias ⟨farFromTriangleFree.le_card_sub_card, _⟩ := farFromTriangleFree_iff
#align simple_graph.far_from_triangle_free.le_card_sub_card SimpleGraph.farFromTriangleFree.le_card_sub_card

nonrec theorem FarFromTriangleFree.mono (hε : G.FarFromTriangleFree ε) (h : δ ≤ ε) :
    G.FarFromTriangleFree δ := hε.mono <| by gcongr
#align simple_graph.far_from_triangle_free.mono SimpleGraph.FarFromTriangleFree.mono

theorem FarFromTriangleFree.cliqueFinset_nonempty' (hH : H ≤ G) (hG : G.FarFromTriangleFree ε)
    (hcard : (G.edgeFinset.card - H.edgeFinset.card : 𝕜) < ε * (card α ^ 2 : ℕ)) :
    (H.cliqueFinset 3).Nonempty :=
  nonempty_of_ne_empty <|
    cliqueFinset_eq_empty_iff.not.2 fun hH' => (hG.le_card_sub_card hH hH').not_lt hcard
#align simple_graph.far_from_triangle_free.clique_finset_nonempty' SimpleGraph.FarFromTriangleFree.cliqueFinset_nonempty'

variable [Nonempty α]

theorem FarFromTriangleFree.nonpos (h₀ : G.FarFromTriangleFree ε) (h₁ : G.CliqueFree 3) :
    ε ≤ 0 := by
  have := h₀ (empty_subset _)
  rw [coe_empty, Finset.card_empty, cast_zero, deleteEdges_empty_eq] at this
  exact nonpos_of_mul_nonpos_left (this h₁) (cast_pos.2 <| sq_pos_of_pos Fintype.card_pos)
#align simple_graph.far_from_triangle_free.nonpos SimpleGraph.FarFromTriangleFree.nonpos

theorem CliqueFree.not_farFromTriangleFree (hG : G.CliqueFree 3) (hε : 0 < ε) :
    ¬G.FarFromTriangleFree ε := fun h => (h.nonpos hG).not_lt hε
#align simple_graph.clique_free.not_far_from_triangle_free SimpleGraph.CliqueFree.not_farFromTriangleFree

theorem FarFromTriangleFree.not_cliqueFree (hG : G.FarFromTriangleFree ε) (hε : 0 < ε) :
    ¬G.CliqueFree 3 := fun h => (hG.nonpos h).not_lt hε
#align simple_graph.far_from_triangle_free.not_clique_free SimpleGraph.FarFromTriangleFree.not_cliqueFree

theorem FarFromTriangleFree.cliqueFinset_nonempty (hG : G.FarFromTriangleFree ε) (hε : 0 < ε) :
    (G.cliqueFinset 3).Nonempty :=
  nonempty_of_ne_empty <| cliqueFinset_eq_empty_iff.not.2 <| hG.not_cliqueFree hε
#align simple_graph.far_from_triangle_free.clique_finset_nonempty SimpleGraph.FarFromTriangleFree.cliqueFinset_nonempty

end SimpleGraph
