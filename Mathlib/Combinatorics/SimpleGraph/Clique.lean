/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Pairwise

#align_import combinatorics.simple_graph.clique from "leanprover-community/mathlib"@"cd7f0626a0b04be1dda223a26123313514a55fb4"

/-!
# Graph cliques

This file defines cliques in simple graphs. A clique is a set of vertices that are pairwise
adjacent.

## Main declarations

* `SimpleGraph.IsClique`: Predicate for a set of vertices to be a clique.
* `SimpleGraph.IsNClique`: Predicate for a set of vertices to be an `n`-clique.
* `SimpleGraph.cliqueFinset`: Finset of `n`-cliques of a graph.
* `SimpleGraph.CliqueFree`: Predicate for a graph to have no `n`-cliques.

## TODO

* Clique numbers
* Do we need `cliqueSet`, a version of `cliqueFinset` for infinite graphs?
-/


open Finset Fintype

namespace SimpleGraph

variable {α : Type*} (G H : SimpleGraph α)

/-! ### Cliques -/


section Clique

variable {s t : Set α}

/-- A clique in a graph is a set of vertices that are pairwise adjacent. -/
abbrev IsClique (s : Set α) : Prop :=
  s.Pairwise G.Adj
#align simple_graph.is_clique SimpleGraph.IsClique

theorem isClique_iff : G.IsClique s ↔ s.Pairwise G.Adj :=
  Iff.rfl
#align simple_graph.is_clique_iff SimpleGraph.isClique_iff

/-- A clique is a set of vertices whose induced graph is complete. -/
theorem isClique_iff_induce_eq : G.IsClique s ↔ G.induce s = ⊤ := by
  rw [isClique_iff]
  constructor
  · intro h
    ext ⟨v, hv⟩ ⟨w, hw⟩
    simp only [comap_adj, Subtype.coe_mk, top_adj, Ne.def, Subtype.mk_eq_mk]
    exact ⟨Adj.ne, h hv hw⟩
  · intro h v hv w hw hne
    have h2 : (G.induce s).Adj ⟨v, hv⟩ ⟨w, hw⟩ = _ := rfl
    conv_lhs at h2 => rw [h]
    simp only [top_adj, ne_eq, Subtype.mk.injEq, eq_iff_iff] at h2
    exact h2.1 hne
#align simple_graph.is_clique_iff_induce_eq SimpleGraph.isClique_iff_induce_eq

instance [DecidableEq α] [DecidableRel G.Adj] {s : Finset α} : Decidable (G.IsClique s) :=
  decidable_of_iff' _ G.isClique_iff

variable {G H}

theorem IsClique.mono (h : G ≤ H) : G.IsClique s → H.IsClique s := by
  simp_rw [isClique_iff]
  exact Set.Pairwise.mono' h
#align simple_graph.is_clique.mono SimpleGraph.IsClique.mono

theorem IsClique.subset (h : t ⊆ s) : G.IsClique s → G.IsClique t := by
  simp_rw [isClique_iff]
  exact Set.Pairwise.mono h
#align simple_graph.is_clique.subset SimpleGraph.IsClique.subset

@[simp]
theorem isClique_bot_iff : (⊥ : SimpleGraph α).IsClique s ↔ (s : Set α).Subsingleton :=
  Set.pairwise_bot_iff
#align simple_graph.is_clique_bot_iff SimpleGraph.isClique_bot_iff

alias ⟨IsClique.subsingleton, _⟩ := isClique_bot_iff
#align simple_graph.is_clique.subsingleton SimpleGraph.IsClique.subsingleton

end Clique

/-! ### `n`-cliques -/


section NClique

variable {n : ℕ} {s : Finset α}

/-- An `n`-clique in a graph is a set of `n` vertices which are pairwise connected. -/
structure IsNClique (n : ℕ) (s : Finset α) : Prop where
  clique : G.IsClique s
  card_eq : s.card = n
#align simple_graph.is_n_clique SimpleGraph.IsNClique

theorem isNClique_iff : G.IsNClique n s ↔ G.IsClique s ∧ s.card = n :=
  ⟨fun h ↦ ⟨h.1, h.2⟩, fun h ↦ ⟨h.1, h.2⟩⟩
#align simple_graph.is_n_clique_iff SimpleGraph.isNClique_iff

instance [DecidableEq α] [DecidableRel G.Adj] {n : ℕ} {s : Finset α} :
    Decidable (G.IsNClique n s) :=
  decidable_of_iff' _ G.isNClique_iff

variable {G H}

theorem IsNClique.mono (h : G ≤ H) : G.IsNClique n s → H.IsNClique n s := by
  simp_rw [isNClique_iff]
  exact And.imp_left (IsClique.mono h)
#align simple_graph.is_n_clique.mono SimpleGraph.IsNClique.mono

@[simp]
theorem isNClique_bot_iff : (⊥ : SimpleGraph α).IsNClique n s ↔ n ≤ 1 ∧ s.card = n := by
  rw [isNClique_iff, isClique_bot_iff]
  refine' and_congr_left _
  rintro rfl
  exact card_le_one.symm
#align simple_graph.is_n_clique_bot_iff SimpleGraph.isNClique_bot_iff

variable [DecidableEq α] {a b c : α}

theorem is3Clique_triple_iff : G.IsNClique 3 {a, b, c} ↔ G.Adj a b ∧ G.Adj a c ∧ G.Adj b c := by
  simp only [isNClique_iff, isClique_iff, Set.pairwise_insert_of_symmetric G.symm, coe_insert]
  by_cases hab : a = b <;> by_cases hbc : b = c <;> by_cases hac : a = c <;> subst_vars <;>
    simp [G.ne_of_adj, and_rotate, *]
#align simple_graph.is_3_clique_triple_iff SimpleGraph.is3Clique_triple_iff

theorem is3Clique_iff :
    G.IsNClique 3 s ↔ ∃ a b c, G.Adj a b ∧ G.Adj a c ∧ G.Adj b c ∧ s = {a, b, c} := by
  refine' ⟨fun h ↦ _, _⟩
  · obtain ⟨a, b, c, -, -, -, hs⟩ := card_eq_three.1 h.card_eq
    refine' ⟨a, b, c, _⟩
    rwa [hs, eq_self_iff_true, and_true, is3Clique_triple_iff.symm, ← hs]
  · rintro ⟨a, b, c, hab, hbc, hca, rfl⟩
    exact is3Clique_triple_iff.2 ⟨hab, hbc, hca⟩
#align simple_graph.is_3_clique_iff SimpleGraph.is3Clique_iff

end NClique

/-! ### Graphs without cliques -/


section CliqueFree

variable {m n : ℕ}

/-- `G.CliqueFree n` means that `G` has no `n`-cliques. -/
def CliqueFree (n : ℕ) : Prop :=
  ∀ t, ¬G.IsNClique n t
#align simple_graph.clique_free SimpleGraph.CliqueFree

variable {G H} {s : Finset α}

theorem IsNClique.not_cliqueFree (hG : G.IsNClique n s) : ¬G.CliqueFree n :=
  fun h ↦ h _ hG
#align simple_graph.is_n_clique.not_clique_free SimpleGraph.IsNClique.not_cliqueFree

theorem not_cliqueFree_of_top_embedding {n : ℕ} (f : (⊤ : SimpleGraph (Fin n)) ↪g G) :
    ¬G.CliqueFree n := by
  simp only [CliqueFree, isNClique_iff, isClique_iff_induce_eq, not_forall, Classical.not_not]
  use Finset.univ.map f.toEmbedding
  simp only [card_map, Finset.card_fin, eq_self_iff_true, and_true_iff]
  ext ⟨v, hv⟩ ⟨w, hw⟩
  simp only [coe_map, Set.mem_image, coe_univ, Set.mem_univ, true_and_iff] at hv hw
  obtain ⟨v', rfl⟩ := hv
  obtain ⟨w', rfl⟩ := hw
  simp only [coe_sort_coe, RelEmbedding.coe_toEmbedding, comap_adj, Function.Embedding.coe_subtype,
    f.map_adj_iff, top_adj, ne_eq, Subtype.mk.injEq, RelEmbedding.inj]
  -- This used to be the end of the proof before leanprover/lean4#2644
  erw [Function.Embedding.coe_subtype, f.map_adj_iff]
  simp
#align simple_graph.not_clique_free_of_top_embedding SimpleGraph.not_cliqueFree_of_top_embedding

/-- An embedding of a complete graph that witnesses the fact that the graph is not clique-free. -/
noncomputable def topEmbeddingOfNotCliqueFree {n : ℕ} (h : ¬G.CliqueFree n) :
    (⊤ : SimpleGraph (Fin n)) ↪g G := by
  simp only [CliqueFree, isNClique_iff, isClique_iff_induce_eq, not_forall, Classical.not_not] at h
  obtain ⟨ha, hb⟩ := h.choose_spec
  have : (⊤ : SimpleGraph (Fin h.choose.card)) ≃g (⊤ : SimpleGraph h.choose) := by
    apply Iso.completeGraph
    simpa using (Fintype.equivFin h.choose).symm
  rw [← ha] at this
  convert (Embedding.induce ↑h.choose.toSet).comp this.toEmbedding
  exact hb.symm
#align simple_graph.top_embedding_of_not_clique_free SimpleGraph.topEmbeddingOfNotCliqueFree

theorem not_cliqueFree_iff (n : ℕ) : ¬G.CliqueFree n ↔ Nonempty ((⊤ : SimpleGraph (Fin n)) ↪g G) :=
  ⟨fun h ↦ ⟨topEmbeddingOfNotCliqueFree h⟩, fun ⟨f⟩ ↦ not_cliqueFree_of_top_embedding f⟩
#align simple_graph.not_clique_free_iff SimpleGraph.not_cliqueFree_iff

theorem cliqueFree_iff {n : ℕ} : G.CliqueFree n ↔ IsEmpty ((⊤ : SimpleGraph (Fin n)) ↪g G) := by
  rw [← not_iff_not, not_cliqueFree_iff, not_isEmpty_iff]
#align simple_graph.clique_free_iff SimpleGraph.cliqueFree_iff

theorem not_cliqueFree_card_of_top_embedding [Fintype α] (f : (⊤ : SimpleGraph α) ↪g G) :
    ¬G.CliqueFree (card α) := by
  rw [not_cliqueFree_iff]
  exact ⟨(Iso.completeGraph (Fintype.equivFin α)).symm.toEmbedding.trans f⟩
#align simple_graph.not_clique_free_card_of_top_embedding SimpleGraph.not_cliqueFree_card_of_top_embedding

theorem cliqueFree_bot (h : 2 ≤ n) : (⊥ : SimpleGraph α).CliqueFree n := by
  intro t ht
  have := le_trans h (isNClique_bot_iff.1 ht).1
  contradiction
#align simple_graph.clique_free_bot SimpleGraph.cliqueFree_bot

theorem CliqueFree.mono (h : m ≤ n) : G.CliqueFree m → G.CliqueFree n := by
  intro hG s hs
  obtain ⟨t, hts, ht⟩ := s.exists_smaller_set _ (h.trans hs.card_eq.ge)
  exact hG _ ⟨hs.clique.subset hts, ht⟩
#align simple_graph.clique_free.mono SimpleGraph.CliqueFree.mono

theorem CliqueFree.anti (h : G ≤ H) : H.CliqueFree n → G.CliqueFree n :=
  forall_imp fun _ ↦ mt <| IsNClique.mono h
#align simple_graph.clique_free.anti SimpleGraph.CliqueFree.anti

/-- See `SimpleGraph.cliqueFree_of_chromaticNumber_lt` for a tighter bound. -/
theorem cliqueFree_of_card_lt [Fintype α] (hc : card α < n) : G.CliqueFree n := by
  by_contra h
  refine' Nat.lt_le_asymm hc _
  rw [cliqueFree_iff, not_isEmpty_iff] at h
  simpa only [Fintype.card_fin] using Fintype.card_le_of_embedding h.some.toEmbedding
#align simple_graph.clique_free_of_card_lt SimpleGraph.cliqueFree_of_card_lt

/-- A complete `r`-partite graph has no `n`-cliques for `r < n`. -/
theorem cliqueFree_completeMultipartiteGraph {ι : Type*} [Fintype ι] (V : ι → Type*)
    (hc : card ι < n) : (completeMultipartiteGraph V).CliqueFree n := by
  rw [cliqueFree_iff, isEmpty_iff]
  intro f
  obtain ⟨v, w, hn, he⟩ := exists_ne_map_eq_of_card_lt (Sigma.fst ∘ f) (by simp [hc])
  rw [← top_adj, ← f.map_adj_iff, comap_adj, top_adj] at hn
  exact absurd he hn

/-- Clique-freeness is preserved by `replaceVertex`. -/
theorem cliqueFree_of_replaceVertex_cliqueFree [DecidableEq α] (s t : α) (h : G.CliqueFree n) :
    (G.replaceVertex s t).CliqueFree n := by
  contrapose h
  obtain ⟨⟨f, hi⟩, ha⟩ := topEmbeddingOfNotCliqueFree h
  simp only [Function.Embedding.coeFn_mk, top_adj, ne_eq] at ha
  rw [not_cliqueFree_iff]
  by_cases mt : t ∈ Set.range f
  · obtain ⟨x, hx⟩ := mt
    by_cases ms : s ∈ Set.range f
    · obtain ⟨y, hy⟩ := ms
      by_cases hst : s = t
      · simp_all [not_cliqueFree_iff]
      · replace ha := @ha x y; simp_all
    · use ⟨fun v => if v = x then s else f v, ?_⟩
      swap
      · intro a b
        dsimp only
        split_ifs
        · simp_all
        · intro; simp_all
        · intro; simp_all
        · apply hi
      intro a b
      simp only [Function.Embedding.coeFn_mk, top_adj, ne_eq]
      split_ifs with h1 h2 h2
      · simp_all
      · have := (@ha b x).mpr h2
        split_ifs at this; subst h1; tauto
      · have := (@ha a x).mpr h1
        split_ifs at this; subst h2; tauto
      · rw [← @ha a b]
        have := (@hi a x).mt h1
        have := (@hi b x).mt h2
        simp_all
  · use ⟨f, hi⟩; simp_all

end CliqueFree

/-! ### Set of cliques -/


section CliqueSet

variable {n : ℕ} {a b c : α} {s : Finset α}

/-- The `n`-cliques in a graph as a set. -/
def cliqueSet (n : ℕ) : Set (Finset α) :=
  { s | G.IsNClique n s }
#align simple_graph.clique_set SimpleGraph.cliqueSet

theorem mem_cliqueSet_iff : s ∈ G.cliqueSet n ↔ G.IsNClique n s :=
  Iff.rfl
#align simple_graph.mem_clique_set_iff SimpleGraph.mem_cliqueSet_iff

@[simp]
theorem cliqueSet_eq_empty_iff : G.cliqueSet n = ∅ ↔ G.CliqueFree n := by
  simp_rw [CliqueFree, Set.eq_empty_iff_forall_not_mem, mem_cliqueSet_iff]
#align simple_graph.clique_set_eq_empty_iff SimpleGraph.cliqueSet_eq_empty_iff

alias ⟨_, CliqueFree.cliqueSet⟩ := cliqueSet_eq_empty_iff
#align simple_graph.clique_free.clique_set SimpleGraph.CliqueFree.cliqueSet

--attribute [protected] CliqueFree.cliqueSet -- porting note: removed

variable {G H}

@[mono]
theorem cliqueSet_mono (h : G ≤ H) : G.cliqueSet n ⊆ H.cliqueSet n :=
  fun _ ↦ IsNClique.mono h
#align simple_graph.clique_set_mono SimpleGraph.cliqueSet_mono

theorem cliqueSet_mono' (h : G ≤ H) : G.cliqueSet ≤ H.cliqueSet :=
  fun _ ↦ cliqueSet_mono h
#align simple_graph.clique_set_mono' SimpleGraph.cliqueSet_mono'

end CliqueSet

/-! ### Finset of cliques -/


section CliqueFinset

variable [Fintype α] [DecidableEq α] [DecidableRel G.Adj] {n : ℕ} {a b c : α} {s : Finset α}

/-- The `n`-cliques in a graph as a finset. -/
def cliqueFinset (n : ℕ) : Finset (Finset α) :=
  univ.filter <| G.IsNClique n
#align simple_graph.clique_finset SimpleGraph.cliqueFinset

theorem mem_cliqueFinset_iff : s ∈ G.cliqueFinset n ↔ G.IsNClique n s :=
  mem_filter.trans <| and_iff_right <| mem_univ _
#align simple_graph.mem_clique_finset_iff SimpleGraph.mem_cliqueFinset_iff

@[simp]
theorem coe_cliqueFinset (n : ℕ) : (G.cliqueFinset n : Set (Finset α)) = G.cliqueSet n :=
  Set.ext fun _ ↦ mem_cliqueFinset_iff _
#align simple_graph.coe_clique_finset SimpleGraph.coe_cliqueFinset

@[simp]
theorem cliqueFinset_eq_empty_iff : G.cliqueFinset n = ∅ ↔ G.CliqueFree n := by
  simp_rw [CliqueFree, eq_empty_iff_forall_not_mem, mem_cliqueFinset_iff]
#align simple_graph.clique_finset_eq_empty_iff SimpleGraph.cliqueFinset_eq_empty_iff

alias ⟨_, CliqueFree.cliqueFinset⟩ := cliqueFinset_eq_empty_iff
#align simple_graph.clique_free.clique_finset SimpleGraph.CliqueFree.cliqueFinset

--attribute [protected] CliqueFree.cliqueFinset -- porting note: removed

variable {G} [DecidableRel H.Adj]

@[mono]
theorem cliqueFinset_mono (h : G ≤ H) : G.cliqueFinset n ⊆ H.cliqueFinset n :=
  monotone_filter_right _ fun _ ↦ IsNClique.mono h
#align simple_graph.clique_finset_mono SimpleGraph.cliqueFinset_mono

end CliqueFinset

end SimpleGraph
