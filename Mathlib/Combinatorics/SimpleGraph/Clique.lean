/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta

! This file was ported from Lean 3 source module combinatorics.simple_graph.clique
! leanprover-community/mathlib commit cd7f0626a0b04be1dda223a26123313514a55fb4
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Combinatorics.SimpleGraph.Basic
import Mathbin.Data.Finset.Pairwise

/-!
# Graph cliques

This file defines cliques in simple graphs. A clique is a set of vertices that are pairwise
adjacent.

## Main declarations

* `simple_graph.is_clique`: Predicate for a set of vertices to be a clique.
* `simple_graph.is_n_clique`: Predicate for a set of vertices to be a `n`-clique.
* `simple_graph.clique_finset`: Finset of `n`-cliques of a graph.
* `simple_graph.clique_free`: Predicate for a graph to have no `n`-cliques.

## TODO

* Clique numbers
* Do we need `clique_set`, a version of `clique_finset` for infinite graphs?
-/


open Finset Fintype

namespace SimpleGraph

variable {α : Type _} (G H : SimpleGraph α)

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
theorem isClique_iff_induce_eq : G.IsClique s ↔ G.induce s = ⊤ :=
  by
  rw [is_clique_iff]
  constructor
  · intro h
    ext (⟨v, hv⟩⟨w, hw⟩)
    simp only [comap_adj, Subtype.coe_mk, top_adj, Ne.def, Subtype.mk_eq_mk]
    exact ⟨adj.ne, h hv hw⟩
  · intro h v hv w hw hne
    have : (G.induce s).Adj ⟨v, hv⟩ ⟨w, hw⟩ = _ := rfl
    conv_lhs at this => rw [h]
    simpa [hne]
#align simple_graph.is_clique_iff_induce_eq SimpleGraph.isClique_iff_induce_eq

instance [DecidableEq α] [DecidableRel G.Adj] {s : Finset α} : Decidable (G.IsClique s) :=
  decidable_of_iff' _ G.isClique_iff

variable {G H}

theorem IsClique.mono (h : G ≤ H) : G.IsClique s → H.IsClique s :=
  by
  simp_rw [is_clique_iff]
  exact Set.Pairwise.mono' h
#align simple_graph.is_clique.mono SimpleGraph.IsClique.mono

theorem IsClique.subset (h : t ⊆ s) : G.IsClique s → G.IsClique t :=
  by
  simp_rw [is_clique_iff]
  exact Set.Pairwise.mono h
#align simple_graph.is_clique.subset SimpleGraph.IsClique.subset

@[simp]
theorem isClique_bot_iff : (⊥ : SimpleGraph α).IsClique s ↔ (s : Set α).Subsingleton :=
  Set.pairwise_bot_iff
#align simple_graph.is_clique_bot_iff SimpleGraph.isClique_bot_iff

alias is_clique_bot_iff ↔ is_clique.subsingleton _
#align simple_graph.is_clique.subsingleton SimpleGraph.IsClique.subsingleton

end Clique

/-! ### `n`-cliques -/


section NClique

variable {n : ℕ} {s : Finset α}

/-- A `n`-clique in a graph is a set of `n` vertices which are pairwise connected. -/
structure IsNClique (n : ℕ) (s : Finset α) : Prop where
  clique : G.IsClique s
  card_eq : s.card = n
#align simple_graph.is_n_clique SimpleGraph.IsNClique

theorem isNClique_iff : G.IsNClique n s ↔ G.IsClique s ∧ s.card = n :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩
#align simple_graph.is_n_clique_iff SimpleGraph.isNClique_iff

instance [DecidableEq α] [DecidableRel G.Adj] {n : ℕ} {s : Finset α} :
    Decidable (G.IsNClique n s) :=
  decidable_of_iff' _ G.isNClique_iff

variable {G H}

theorem IsNClique.mono (h : G ≤ H) : G.IsNClique n s → H.IsNClique n s :=
  by
  simp_rw [is_n_clique_iff]
  exact And.imp_left (is_clique.mono h)
#align simple_graph.is_n_clique.mono SimpleGraph.IsNClique.mono

@[simp]
theorem isNClique_bot_iff : (⊥ : SimpleGraph α).IsNClique n s ↔ n ≤ 1 ∧ s.card = n :=
  by
  rw [is_n_clique_iff, is_clique_bot_iff]
  refine' and_congr_left _
  rintro rfl
  exact card_le_one.symm
#align simple_graph.is_n_clique_bot_iff SimpleGraph.isNClique_bot_iff

variable [DecidableEq α] {a b c : α}

theorem is_3_clique_triple_iff : G.IsNClique 3 {a, b, c} ↔ G.Adj a b ∧ G.Adj a c ∧ G.Adj b c :=
  by
  simp only [is_n_clique_iff, is_clique_iff, Set.pairwise_insert_of_symmetric G.symm, coe_insert]
  have : ¬1 + 1 = 3 := by norm_num
  by_cases hab : a = b <;> by_cases hbc : b = c <;> by_cases hac : a = c <;> subst_vars <;>
    simp [G.ne_of_adj, and_rotate, *]
#align simple_graph.is_3_clique_triple_iff SimpleGraph.is_3_clique_triple_iff

theorem is_3_clique_iff :
    G.IsNClique 3 s ↔ ∃ a b c, G.Adj a b ∧ G.Adj a c ∧ G.Adj b c ∧ s = {a, b, c} :=
  by
  refine' ⟨fun h => _, _⟩
  · obtain ⟨a, b, c, -, -, -, rfl⟩ := card_eq_three.1 h.card_eq
    refine' ⟨a, b, c, _⟩
    rw [is_3_clique_triple_iff] at h
    tauto
  · rintro ⟨a, b, c, hab, hbc, hca, rfl⟩
    exact is_3_clique_triple_iff.2 ⟨hab, hbc, hca⟩
#align simple_graph.is_3_clique_iff SimpleGraph.is_3_clique_iff

end NClique

/-! ### Graphs without cliques -/


section CliqueFree

variable {m n : ℕ}

/-- `G.clique_free n` means that `G` has no `n`-cliques. -/
def CliqueFree (n : ℕ) : Prop :=
  ∀ t, ¬G.IsNClique n t
#align simple_graph.clique_free SimpleGraph.CliqueFree

variable {G H} {s : Finset α}

theorem IsNClique.not_cliqueFree (hG : G.IsNClique n s) : ¬G.CliqueFree n := fun h => h _ hG
#align simple_graph.is_n_clique.not_clique_free SimpleGraph.IsNClique.not_cliqueFree

theorem not_cliqueFree_of_top_embedding {n : ℕ} (f : (⊤ : SimpleGraph (Fin n)) ↪g G) :
    ¬G.CliqueFree n :=
  by
  simp only [clique_free, is_n_clique_iff, is_clique_iff_induce_eq, not_forall, Classical.not_not]
  use finset.univ.map f.to_embedding
  simp only [card_map, Finset.card_fin, eq_self_iff_true, and_true_iff]
  ext (⟨v, hv⟩⟨w, hw⟩)
  simp only [coe_map, RelEmbedding.coeFn_toEmbedding, Set.mem_image, coe_univ, Set.mem_univ,
    true_and_iff] at hv hw
  obtain ⟨v', rfl⟩ := hv
  obtain ⟨w', rfl⟩ := hw
  simp only [f.map_adj_iff, comap_adj, Function.Embedding.coe_subtype, Subtype.coe_mk, top_adj,
    Ne.def, Subtype.mk_eq_mk]
  exact (Function.Embedding.apply_eq_iff_eq _ _ _).symm.Not
#align simple_graph.not_clique_free_of_top_embedding SimpleGraph.not_cliqueFree_of_top_embedding

/-- An embedding of a complete graph that witnesses the fact that the graph is not clique-free. -/
noncomputable def topEmbeddingOfNotCliqueFree {n : ℕ} (h : ¬G.CliqueFree n) :
    (⊤ : SimpleGraph (Fin n)) ↪g G :=
  by
  simp only [clique_free, is_n_clique_iff, is_clique_iff_induce_eq, not_forall,
    Classical.not_not] at h
  obtain ⟨ha, hb⟩ := h.some_spec
  have : (⊤ : SimpleGraph (Fin h.some.card)) ≃g (⊤ : SimpleGraph h.some) :=
    by
    apply iso.complete_graph
    simpa using (Fintype.equivFin h.some).symm
  rw [← ha] at this
  convert (embedding.induce ↑h.some).comp this.to_embedding <;> exact hb.symm
#align simple_graph.top_embedding_of_not_clique_free SimpleGraph.topEmbeddingOfNotCliqueFree

theorem not_cliqueFree_iff (n : ℕ) : ¬G.CliqueFree n ↔ Nonempty ((⊤ : SimpleGraph (Fin n)) ↪g G) :=
  by
  constructor
  · exact fun h => ⟨top_embedding_of_not_clique_free h⟩
  · rintro ⟨f⟩
    exact not_clique_free_of_top_embedding f
#align simple_graph.not_clique_free_iff SimpleGraph.not_cliqueFree_iff

theorem cliqueFree_iff {n : ℕ} : G.CliqueFree n ↔ IsEmpty ((⊤ : SimpleGraph (Fin n)) ↪g G) := by
  rw [← not_iff_not, not_clique_free_iff, not_isEmpty_iff]
#align simple_graph.clique_free_iff SimpleGraph.cliqueFree_iff

theorem not_cliqueFree_card_of_top_embedding [Fintype α] (f : (⊤ : SimpleGraph α) ↪g G) :
    ¬G.CliqueFree (card α) := by
  rw [not_clique_free_iff]
  use (iso.complete_graph (Fintype.equivFin α)).symm.toEmbedding.trans f
#align simple_graph.not_clique_free_card_of_top_embedding SimpleGraph.not_cliqueFree_card_of_top_embedding

theorem cliqueFree_bot (h : 2 ≤ n) : (⊥ : SimpleGraph α).CliqueFree n :=
  by
  rintro t ht
  rw [is_n_clique_bot_iff] at ht
  linarith
#align simple_graph.clique_free_bot SimpleGraph.cliqueFree_bot

theorem CliqueFree.mono (h : m ≤ n) : G.CliqueFree m → G.CliqueFree n :=
  by
  rintro hG s hs
  obtain ⟨t, hts, ht⟩ := s.exists_smaller_set _ (h.trans hs.card_eq.ge)
  exact hG _ ⟨hs.clique.subset hts, ht⟩
#align simple_graph.clique_free.mono SimpleGraph.CliqueFree.mono

theorem CliqueFree.anti (h : G ≤ H) : H.CliqueFree n → G.CliqueFree n :=
  forall_imp fun s => mt <| IsNClique.mono h
#align simple_graph.clique_free.anti SimpleGraph.CliqueFree.anti

/-- See `simple_graph.clique_free_chromatic_number_succ` for a tighter bound. -/
theorem cliqueFree_of_card_lt [Fintype α] (hc : card α < n) : G.CliqueFree n :=
  by
  by_contra h
  refine' Nat.lt_le_antisymm hc _
  rw [clique_free_iff, not_isEmpty_iff] at h
  simpa using Fintype.card_le_of_embedding h.some.to_embedding
#align simple_graph.clique_free_of_card_lt SimpleGraph.cliqueFree_of_card_lt

end CliqueFree

/-! ### Set of cliques -/


section CliqueSet

variable (G) {n : ℕ} {a b c : α} {s : Finset α}

/-- The `n`-cliques in a graph as a set. -/
def cliqueSet (n : ℕ) : Set (Finset α) :=
  { s | G.IsNClique n s }
#align simple_graph.clique_set SimpleGraph.cliqueSet

theorem mem_cliqueSet_iff : s ∈ G.cliqueSet n ↔ G.IsNClique n s :=
  Iff.rfl
#align simple_graph.mem_clique_set_iff SimpleGraph.mem_cliqueSet_iff

@[simp]
theorem cliqueSet_eq_empty_iff : G.cliqueSet n = ∅ ↔ G.CliqueFree n := by
  simp_rw [clique_free, Set.eq_empty_iff_forall_not_mem, mem_clique_set_iff]
#align simple_graph.clique_set_eq_empty_iff SimpleGraph.cliqueSet_eq_empty_iff

alias clique_set_eq_empty_iff ↔ _ clique_free.clique_set
#align simple_graph.clique_free.clique_set SimpleGraph.CliqueFree.cliqueSet

attribute [protected] clique_free.clique_set

variable {G H}

@[mono]
theorem cliqueSet_mono (h : G ≤ H) : G.cliqueSet n ⊆ H.cliqueSet n := fun _ => IsNClique.mono h
#align simple_graph.clique_set_mono SimpleGraph.cliqueSet_mono

theorem cliqueSet_mono' (h : G ≤ H) : G.cliqueSet ≤ H.cliqueSet := fun _ => cliqueSet_mono h
#align simple_graph.clique_set_mono' SimpleGraph.cliqueSet_mono'

end CliqueSet

/-! ### Finset of cliques -/


section CliqueFinset

variable (G) [Fintype α] [DecidableEq α] [DecidableRel G.Adj] {n : ℕ} {a b c : α} {s : Finset α}

/-- The `n`-cliques in a graph as a finset. -/
def cliqueFinset (n : ℕ) : Finset (Finset α) :=
  univ.filterₓ <| G.IsNClique n
#align simple_graph.clique_finset SimpleGraph.cliqueFinset

theorem mem_cliqueFinset_iff : s ∈ G.cliqueFinset n ↔ G.IsNClique n s :=
  mem_filter.trans <| and_iff_right <| mem_univ _
#align simple_graph.mem_clique_finset_iff SimpleGraph.mem_cliqueFinset_iff

@[simp]
theorem coe_cliqueFinset (n : ℕ) : (G.cliqueFinset n : Set (Finset α)) = G.cliqueSet n :=
  Set.ext fun _ => mem_cliqueFinset_iff _
#align simple_graph.coe_clique_finset SimpleGraph.coe_cliqueFinset

@[simp]
theorem cliqueFinset_eq_empty_iff : G.cliqueFinset n = ∅ ↔ G.CliqueFree n := by
  simp_rw [clique_free, eq_empty_iff_forall_not_mem, mem_clique_finset_iff]
#align simple_graph.clique_finset_eq_empty_iff SimpleGraph.cliqueFinset_eq_empty_iff

alias clique_finset_eq_empty_iff ↔ _ _root_.simple_graph.clique_free.clique_finset
#align simple_graph.clique_free.clique_finset SimpleGraph.CliqueFree.cliqueFinset

attribute [protected] clique_free.clique_finset

variable {G} [DecidableRel H.Adj]

@[mono]
theorem cliqueFinset_mono (h : G ≤ H) : G.cliqueFinset n ⊆ H.cliqueFinset n :=
  monotone_filter_right _ fun _ => IsNClique.mono h
#align simple_graph.clique_finset_mono SimpleGraph.cliqueFinset_mono

end CliqueFinset

end SimpleGraph

