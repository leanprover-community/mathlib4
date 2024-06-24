/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import Mathlib.Combinatorics.SimpleGraph.Connectivity
import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Data.Finset.Pairwise

#align_import combinatorics.simple_graph.clique from "leanprover-community/mathlib"@"3365b20c2ffa7c35e47e5209b89ba9abdddf3ffe"

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
* Dualise all the API to get independent sets
-/


open Finset Fintype Function SimpleGraph.Walk

namespace SimpleGraph

variable {α β : Type*} (G H : SimpleGraph α)

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
    simp only [comap_adj, Subtype.coe_mk, top_adj, Ne, Subtype.mk_eq_mk]
    exact ⟨Adj.ne, h hv hw⟩
  · intro h v hv w hw hne
    have h2 : (G.induce s).Adj ⟨v, hv⟩ ⟨w, hw⟩ = _ := rfl
    conv_lhs at h2 => rw [h]
    simp only [top_adj, ne_eq, Subtype.mk.injEq, eq_iff_iff] at h2
    exact h2.1 hne
#align simple_graph.is_clique_iff_induce_eq SimpleGraph.isClique_iff_induce_eq

instance [DecidableEq α] [DecidableRel G.Adj] {s : Finset α} : Decidable (G.IsClique s) :=
  decidable_of_iff' _ G.isClique_iff

variable {G H} {a b : α}

lemma isClique_empty : G.IsClique ∅ := by simp
#align simple_graph.is_clique_empty SimpleGraph.isClique_empty

lemma isClique_singleton (a : α) : G.IsClique {a} := by simp
#align simple_graph.is_clique_singleton SimpleGraph.isClique_singleton

theorem IsClique.of_subsingleton {G : SimpleGraph α} (hs : s.Subsingleton) : G.IsClique s :=
  hs.pairwise G.Adj

lemma isClique_pair : G.IsClique {a, b} ↔ a ≠ b → G.Adj a b := Set.pairwise_pair_of_symmetric G.symm
#align simple_graph.is_clique_pair SimpleGraph.isClique_pair

@[simp]
lemma isClique_insert : G.IsClique (insert a s) ↔ G.IsClique s ∧ ∀ b ∈ s, a ≠ b → G.Adj a b :=
  Set.pairwise_insert_of_symmetric G.symm
#align simple_graph.is_clique_insert SimpleGraph.isClique_insert

lemma isClique_insert_of_not_mem (ha : a ∉ s) :
    G.IsClique (insert a s) ↔ G.IsClique s ∧ ∀ b ∈ s, G.Adj a b :=
  Set.pairwise_insert_of_symmetric_of_not_mem G.symm ha
#align simple_graph.is_clique_insert_of_not_mem SimpleGraph.isClique_insert_of_not_mem

lemma IsClique.insert (hs : G.IsClique s) (h : ∀ b ∈ s, a ≠ b → G.Adj a b) :
    G.IsClique (insert a s) := hs.insert_of_symmetric G.symm h
#align simple_graph.is_clique.insert SimpleGraph.IsClique.insert

theorem IsClique.mono (h : G ≤ H) : G.IsClique s → H.IsClique s := Set.Pairwise.mono' h
#align simple_graph.is_clique.mono SimpleGraph.IsClique.mono

theorem IsClique.subset (h : t ⊆ s) : G.IsClique s → G.IsClique t := Set.Pairwise.mono h
#align simple_graph.is_clique.subset SimpleGraph.IsClique.subset

@[simp]
theorem isClique_bot_iff : (⊥ : SimpleGraph α).IsClique s ↔ (s : Set α).Subsingleton :=
  Set.pairwise_bot_iff
#align simple_graph.is_clique_bot_iff SimpleGraph.isClique_bot_iff

alias ⟨IsClique.subsingleton, _⟩ := isClique_bot_iff
#align simple_graph.is_clique.subsingleton SimpleGraph.IsClique.subsingleton

protected theorem IsClique.map (h : G.IsClique s) {f : α ↪ β} : (G.map f).IsClique (f '' s) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
  exact ⟨a, b, h ha hb <| ne_of_apply_ne _ hab, rfl, rfl⟩
#align simple_graph.is_clique.map SimpleGraph.IsClique.map

theorem isClique_map_iff_of_nontrivial {f : α ↪ β} {t : Set β} (ht : t.Nontrivial) :
    (G.map f).IsClique t ↔ ∃ (s : Set α), G.IsClique s ∧ f '' s = t := by
  refine ⟨fun h ↦ ⟨f ⁻¹' t, ?_, ?_⟩, by rintro ⟨x, hs, rfl⟩; exact hs.map⟩
  · rintro x (hx : f x ∈ t) y (hy : f y ∈ t) hne
    obtain ⟨u,v, huv, hux, hvy⟩ := h hx hy (by simpa)
    rw [EmbeddingLike.apply_eq_iff_eq] at hux hvy
    rwa [← hux, ← hvy]
  rw [Set.image_preimage_eq_iff]
  intro x hxt
  obtain ⟨y,hyt, hyne⟩ := ht.exists_ne x
  obtain ⟨u,v, -, rfl, rfl⟩ := h hyt hxt hyne
  exact Set.mem_range_self _

theorem isClique_map_iff {f : α ↪ β} {t : Set β} :
    (G.map f).IsClique t ↔ t.Subsingleton ∨ ∃ (s : Set α), G.IsClique s ∧ f '' s = t := by
  obtain (ht | ht) := t.subsingleton_or_nontrivial
  · simp [IsClique.of_subsingleton, ht]
  simp [isClique_map_iff_of_nontrivial ht, ht.not_subsingleton]

@[simp] theorem isClique_map_image_iff {f : α ↪ β} :
    (G.map f).IsClique (f '' s) ↔ G.IsClique s := by
  rw [isClique_map_iff, f.injective.subsingleton_image_iff]
  obtain (hs | hs) := s.subsingleton_or_nontrivial
  · simp [hs, IsClique.of_subsingleton]
  simp [or_iff_right hs.not_subsingleton, Set.image_eq_image f.injective]
section DecidableEq

variable [DecidableEq β] {f : α ↪ β} {t : Finset β}

theorem isClique_map_finset_iff_of_nontrivial (ht : t.Nontrivial) :
    (G.map f).IsClique t ↔ ∃ (s : Finset α), G.IsClique s ∧ s.map f = t := by
  constructor
  · rw [isClique_map_iff_of_nontrivial (by simpa)]
    rintro ⟨s, hs, hst⟩
    obtain ⟨s, rfl⟩ := Set.Finite.exists_finset_coe <|
      (show s.Finite from Set.Finite.of_finite_image (by simp [hst]) f.injective.injOn)
    exact ⟨s,hs, Finset.coe_inj.1 (by simpa)⟩
  rintro ⟨s, hs, rfl⟩
  simpa using hs.map (f := f)

theorem isClique_map_finset_iff :
    (G.map f).IsClique t ↔ t.card ≤ 1 ∨ ∃ (s : Finset α), G.IsClique s ∧ s.map f = t := by
  obtain (ht | ht) := le_or_lt t.card 1
  · simp only [ht, true_or, iff_true]
    exact IsClique.of_subsingleton <| card_le_one.1 ht
  rw [isClique_map_finset_iff_of_nontrivial, ← not_lt]
  · simp [ht, Finset.map_eq_image]
  exact Finset.one_lt_card_iff_nontrivial.mp ht

protected theorem IsClique.finsetMap {f : α ↪ β} {s : Finset α} (h : G.IsClique s) :
    (G.map f).IsClique (s.map f) := by
  simpa

end DecidableEq

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

variable {G H} {a b c : α}

@[simp] lemma isNClique_empty : G.IsNClique n ∅ ↔ n = 0 := by simp [isNClique_iff, eq_comm]
#align simple_graph.is_n_clique_empty SimpleGraph.isNClique_empty

@[simp]
lemma isNClique_singleton : G.IsNClique n {a} ↔ n = 1 := by simp [isNClique_iff, eq_comm]
#align simple_graph.is_n_clique_singleton SimpleGraph.isNClique_singleton

theorem IsNClique.mono (h : G ≤ H) : G.IsNClique n s → H.IsNClique n s := by
  simp_rw [isNClique_iff]
  exact And.imp_left (IsClique.mono h)
#align simple_graph.is_n_clique.mono SimpleGraph.IsNClique.mono

protected theorem IsNClique.map (h : G.IsNClique n s) {f : α ↪ β} :
    (G.map f).IsNClique n (s.map f) :=
  ⟨by rw [coe_map]; exact h.1.map, (card_map _).trans h.2⟩
#align simple_graph.is_n_clique.map SimpleGraph.IsNClique.map

theorem isNClique_map_iff [DecidableEq β] (hn : 1 < n) {t : Finset β} {f : α ↪ β} :
    (G.map f).IsNClique n t ↔ ∃ s : Finset α, G.IsNClique n s ∧ s.map f = t := by
  rw [isNClique_iff, isClique_map_finset_iff, or_and_right,
    or_iff_right (by rintro ⟨h', rfl⟩; exact h'.not_lt hn)]
  constructor
  · rintro ⟨⟨s, hs, rfl⟩, rfl⟩
    simp [isNClique_iff, hs]
  rintro ⟨s, hs, rfl⟩
  simp [hs.card_eq, hs.clique]

@[simp]
theorem isNClique_bot_iff : (⊥ : SimpleGraph α).IsNClique n s ↔ n ≤ 1 ∧ s.card = n := by
  rw [isNClique_iff, isClique_bot_iff]
  refine and_congr_left ?_
  rintro rfl
  exact card_le_one.symm
#align simple_graph.is_n_clique_bot_iff SimpleGraph.isNClique_bot_iff

@[simp]
theorem isNClique_zero : G.IsNClique 0 s ↔ s = ∅ := by
  simp only [isNClique_iff, Finset.card_eq_zero, and_iff_right_iff_imp]; rintro rfl; simp
#align simple_graph.is_n_clique_zero SimpleGraph.isNClique_zero

@[simp]
theorem isNClique_one : G.IsNClique 1 s ↔ ∃ a, s = {a} := by
  simp only [isNClique_iff, card_eq_one, and_iff_right_iff_imp]; rintro ⟨a, rfl⟩; simp
#align simple_graph.is_n_clique_one SimpleGraph.isNClique_one

section DecidableEq

variable [DecidableEq α]

theorem IsNClique.insert (hs : G.IsNClique n s) (h : ∀ b ∈ s, G.Adj a b) :
    G.IsNClique (n + 1) (insert a s) := by
  constructor
  · push_cast
    exact hs.1.insert fun b hb _ => h _ hb
  · rw [card_insert_of_not_mem fun ha => (h _ ha).ne rfl, hs.2]
#align simple_graph.is_n_clique.insert SimpleGraph.IsNClique.insert

theorem is3Clique_triple_iff : G.IsNClique 3 {a, b, c} ↔ G.Adj a b ∧ G.Adj a c ∧ G.Adj b c := by
  simp only [isNClique_iff, isClique_iff, Set.pairwise_insert_of_symmetric G.symm, coe_insert]
  by_cases hab : a = b <;> by_cases hbc : b = c <;> by_cases hac : a = c <;> subst_vars <;>
    simp [G.ne_of_adj, and_rotate, *]
#align simple_graph.is_3_clique_triple_iff SimpleGraph.is3Clique_triple_iff

theorem is3Clique_iff :
    G.IsNClique 3 s ↔ ∃ a b c, G.Adj a b ∧ G.Adj a c ∧ G.Adj b c ∧ s = {a, b, c} := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨a, b, c, -, -, -, hs⟩ := card_eq_three.1 h.card_eq
    refine ⟨a, b, c, ?_⟩
    rwa [hs, eq_self_iff_true, and_true, is3Clique_triple_iff.symm, ← hs]
  · rintro ⟨a, b, c, hab, hbc, hca, rfl⟩
    exact is3Clique_triple_iff.2 ⟨hab, hbc, hca⟩
#align simple_graph.is_3_clique_iff SimpleGraph.is3Clique_iff

end DecidableEq

theorem is3Clique_iff_exists_cycle_length_three :
    (∃ s : Finset α, G.IsNClique 3 s) ↔ ∃ (u : α) (w : G.Walk u u), w.IsCycle ∧ w.length = 3 := by
  classical
  simp_rw [is3Clique_iff, isCycle_def]
  exact
    ⟨(fun ⟨_, a, _, _, hab, hac, hbc, _⟩ => ⟨a, cons hab (cons hbc (cons hac.symm nil)), by aesop⟩),
    (fun ⟨_, .cons hab (.cons hbc (.cons hca nil)), _, _⟩ => ⟨_, _, _, _, hab, hca.symm, hbc, rfl⟩)⟩

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

@[simp]
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

/-- If a graph is cliquefree, any graph that embeds into it is also cliquefree. -/
theorem CliqueFree.comap {H : SimpleGraph β} (f : H ↪g G) : G.CliqueFree n → H.CliqueFree n := by
  intro h; contrapose h
  exact not_cliqueFree_of_top_embedding <| f.comp (topEmbeddingOfNotCliqueFree h)

@[simp] theorem cliqueFree_map_iff {f : α ↪ β} [DecidableEq β] [Nonempty α] :
    (G.map f).CliqueFree n ↔ G.CliqueFree n := by
  obtain (hle | hlt) := le_or_lt n 1
  · obtain (rfl | rfl) := Nat.le_one_iff_eq_zero_or_eq_one.1 hle
    · simp [CliqueFree]
    simp [CliqueFree, show ∃ (_ : β), True from ⟨f (Classical.arbitrary _), trivial⟩]
  simp [CliqueFree, isNClique_map_iff hlt]

/-- See `SimpleGraph.cliqueFree_of_chromaticNumber_lt` for a tighter bound. -/
theorem cliqueFree_of_card_lt [Fintype α] (hc : card α < n) : G.CliqueFree n := by
  by_contra h
  refine Nat.lt_le_asymm hc ?_
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
protected theorem CliqueFree.replaceVertex [DecidableEq α] (h : G.CliqueFree n) (s t : α) :
    (G.replaceVertex s t).CliqueFree n := by
  contrapose h
  obtain ⟨φ, hφ⟩ := topEmbeddingOfNotCliqueFree h
  rw [not_cliqueFree_iff]
  by_cases mt : t ∈ Set.range φ
  · obtain ⟨x, hx⟩ := mt
    by_cases ms : s ∈ Set.range φ
    · obtain ⟨y, hy⟩ := ms
      have e := @hφ x y
      simp_rw [hx, hy, adj_comm, not_adj_replaceVertex_same, top_adj, false_iff, not_ne_iff] at e
      rwa [← hx, e, hy, replaceVertex_self, not_cliqueFree_iff] at h
    · unfold replaceVertex at hφ
      use φ.setValue x s
      intro a b
      simp only [Embedding.coeFn_mk, Embedding.setValue, not_exists.mp ms, ite_false]
      rw [apply_ite (G.Adj · _), apply_ite (G.Adj _ ·), apply_ite (G.Adj _ ·)]
      convert @hφ a b <;> simp only [← φ.apply_eq_iff_eq, SimpleGraph.irrefl, hx]
  · use φ
    simp_rw [Set.mem_range, not_exists, ← ne_eq] at mt
    conv at hφ => enter [a, b]; rw [G.adj_replaceVertex_iff_of_ne _ (mt a) (mt b)]
    exact hφ

@[simp]
theorem cliqueFree_two : G.CliqueFree 2 ↔ G = ⊥ := by
  classical
  constructor
  · simp_rw [← edgeSet_eq_empty, Set.eq_empty_iff_forall_not_mem, Sym2.forall, mem_edgeSet]
    exact fun h a b hab => h _ ⟨by simpa [hab.ne], card_pair hab.ne⟩
  · rintro rfl
    exact cliqueFree_bot le_rfl
#align simple_graph.clique_free_two SimpleGraph.cliqueFree_two

/-- Adding an edge increases the clique number by at most one. -/
protected theorem CliqueFree.sup_edge (h : G.CliqueFree n) (v w : α) :
    (G ⊔ edge v w).CliqueFree (n + 1) := by
  contrapose h
  obtain ⟨f, ha⟩ := topEmbeddingOfNotCliqueFree h
  simp only [ne_eq, top_adj] at ha
  rw [not_cliqueFree_iff]
  by_cases mw : w ∈ Set.range f
  · obtain ⟨x, hx⟩ := mw
    use ⟨f ∘ x.succAboveEmb, f.2.comp Fin.succAbove_right_injective⟩
    intro a b
    simp_rw [Embedding.coeFn_mk, comp_apply, Fin.succAboveEmb_apply, top_adj]
    have hs := @ha (x.succAbove a) (x.succAbove b)
    have ia : w ≠ f (x.succAbove a) :=
      (hx ▸ f.apply_eq_iff_eq x (x.succAbove a)).ne.mpr (x.succAbove_ne a).symm
    have ib : w ≠ f (x.succAbove b) :=
      (hx ▸ f.apply_eq_iff_eq x (x.succAbove b)).ne.mpr (x.succAbove_ne b).symm
    rw [sup_adj, edge_adj] at hs
    simp only [ia.symm, ib.symm, and_false, false_and, or_false] at hs
    rw [hs, Fin.succAbove_right_inj]
  · use ⟨f ∘ Fin.succEmb n, (f.2.of_comp_iff _).mpr (Fin.succ_injective _)⟩
    intro a b
    simp only [Fin.val_succEmb, Embedding.coeFn_mk, comp_apply, top_adj]
    have hs := @ha a.succ b.succ
    have ia : f a.succ ≠ w := by simp_all
    have ib : f b.succ ≠ w := by simp_all
    rw [sup_adj, edge_adj] at hs
    simp only [ia, ib, and_false, false_and, or_false] at hs
    rw [hs, Fin.succ_inj]

end CliqueFree

section CliqueFreeOn
variable {s s₁ s₂ : Set α} {t : Finset α} {a b : α} {m n : ℕ}

/-- `G.CliqueFreeOn s n` means that `G` has no `n`-cliques contained in `s`. -/
def CliqueFreeOn (G : SimpleGraph α) (s : Set α) (n : ℕ) : Prop :=
  ∀ ⦃t⦄, ↑t ⊆ s → ¬G.IsNClique n t
#align simple_graph.clique_free_on SimpleGraph.CliqueFreeOn

theorem CliqueFreeOn.subset (hs : s₁ ⊆ s₂) (h₂ : G.CliqueFreeOn s₂ n) : G.CliqueFreeOn s₁ n :=
  fun _t hts => h₂ <| hts.trans hs
#align simple_graph.clique_free_on.subset SimpleGraph.CliqueFreeOn.subset

theorem CliqueFreeOn.mono (hmn : m ≤ n) (hG : G.CliqueFreeOn s m) : G.CliqueFreeOn s n := by
  rintro t hts ht
  obtain ⟨u, hut, hu⟩ := t.exists_smaller_set _ (hmn.trans ht.card_eq.ge)
  exact hG ((coe_subset.2 hut).trans hts) ⟨ht.clique.subset hut, hu⟩
#align simple_graph.clique_free_on.mono SimpleGraph.CliqueFreeOn.mono

theorem CliqueFreeOn.anti (hGH : G ≤ H) (hH : H.CliqueFreeOn s n) : G.CliqueFreeOn s n :=
  fun _t hts ht => hH hts <| ht.mono hGH
#align simple_graph.clique_free_on.anti SimpleGraph.CliqueFreeOn.anti

@[simp]
theorem cliqueFreeOn_empty : G.CliqueFreeOn ∅ n ↔ n ≠ 0 := by
  simp [CliqueFreeOn, Set.subset_empty_iff]
#align simple_graph.clique_free_on_empty SimpleGraph.cliqueFreeOn_empty

@[simp]
theorem cliqueFreeOn_singleton : G.CliqueFreeOn {a} n ↔ 1 < n := by
  obtain _ | _ | n := n <;>
    simp [CliqueFreeOn, isNClique_iff, ← subset_singleton_iff', (Nat.succ_ne_zero _).symm]
#align simple_graph.clique_free_on_singleton SimpleGraph.cliqueFreeOn_singleton

@[simp]
theorem cliqueFreeOn_univ : G.CliqueFreeOn Set.univ n ↔ G.CliqueFree n := by
  simp [CliqueFree, CliqueFreeOn]
#align simple_graph.clique_free_on_univ SimpleGraph.cliqueFreeOn_univ

protected theorem CliqueFree.cliqueFreeOn (hG : G.CliqueFree n) : G.CliqueFreeOn s n :=
  fun _t _ ↦ hG _
#align simple_graph.clique_free.clique_free_on SimpleGraph.CliqueFree.cliqueFreeOn

theorem cliqueFreeOn_of_card_lt {s : Finset α} (h : s.card < n) : G.CliqueFreeOn s n :=
  fun _t hts ht => h.not_le <| ht.2.symm.trans_le <| card_mono hts
#align simple_graph.clique_free_on_of_card_lt SimpleGraph.cliqueFreeOn_of_card_lt

-- TODO: Restate using `SimpleGraph.IndepSet` once we have it
@[simp]
theorem cliqueFreeOn_two : G.CliqueFreeOn s 2 ↔ s.Pairwise (G.Adjᶜ) := by
  classical
  refine ⟨fun h a ha b hb _ hab => h ?_ ⟨by simpa [hab.ne], card_pair hab.ne⟩, ?_⟩
  · push_cast
    exact Set.insert_subset_iff.2 ⟨ha, Set.singleton_subset_iff.2 hb⟩
  simp only [CliqueFreeOn, isNClique_iff, card_eq_two, coe_subset, not_and, not_exists]
  rintro h t hst ht a b hab rfl
  simp only [coe_insert, coe_singleton, Set.insert_subset_iff, Set.singleton_subset_iff] at hst
  refine h hst.1 hst.2 hab (ht ?_ ?_ hab) <;> simp
#align simple_graph.clique_free_on_two SimpleGraph.cliqueFreeOn_two

theorem CliqueFreeOn.of_succ (hs : G.CliqueFreeOn s (n + 1)) (ha : a ∈ s) :
    G.CliqueFreeOn (s ∩ G.neighborSet a) n := by
  classical
  refine fun t hts ht => hs ?_ (ht.insert fun b hb => (hts hb).2)
  push_cast
  exact Set.insert_subset_iff.2 ⟨ha, hts.trans Set.inter_subset_left⟩
#align simple_graph.clique_free_on.of_succ SimpleGraph.CliqueFreeOn.of_succ

end CliqueFreeOn

/-! ### Set of cliques -/


section CliqueSet

variable {n : ℕ} {a b c : α} {s : Finset α}

/-- The `n`-cliques in a graph as a set. -/
def cliqueSet (n : ℕ) : Set (Finset α) :=
  { s | G.IsNClique n s }
#align simple_graph.clique_set SimpleGraph.cliqueSet

variable {G H}

@[simp]
theorem mem_cliqueSet_iff : s ∈ G.cliqueSet n ↔ G.IsNClique n s :=
  Iff.rfl
#align simple_graph.mem_clique_set_iff SimpleGraph.mem_cliqueSet_iff

@[simp]
theorem cliqueSet_eq_empty_iff : G.cliqueSet n = ∅ ↔ G.CliqueFree n := by
  simp_rw [CliqueFree, Set.eq_empty_iff_forall_not_mem, mem_cliqueSet_iff]
#align simple_graph.clique_set_eq_empty_iff SimpleGraph.cliqueSet_eq_empty_iff

protected alias ⟨_, CliqueFree.cliqueSet⟩ := cliqueSet_eq_empty_iff
#align simple_graph.clique_free.clique_set SimpleGraph.CliqueFree.cliqueSet

@[mono]
theorem cliqueSet_mono (h : G ≤ H) : G.cliqueSet n ⊆ H.cliqueSet n :=
  fun _ ↦ IsNClique.mono h
#align simple_graph.clique_set_mono SimpleGraph.cliqueSet_mono

theorem cliqueSet_mono' (h : G ≤ H) : G.cliqueSet ≤ H.cliqueSet :=
  fun _ ↦ cliqueSet_mono h
#align simple_graph.clique_set_mono' SimpleGraph.cliqueSet_mono'

@[simp]
theorem cliqueSet_zero (G : SimpleGraph α) : G.cliqueSet 0 = {∅} := Set.ext fun s => by simp
#align simple_graph.clique_set_zero SimpleGraph.cliqueSet_zero

@[simp]
theorem cliqueSet_one (G : SimpleGraph α) : G.cliqueSet 1 = Set.range singleton :=
  Set.ext fun s => by simp [eq_comm]
#align simple_graph.clique_set_one SimpleGraph.cliqueSet_one

@[simp]
theorem cliqueSet_bot (hn : 1 < n) : (⊥ : SimpleGraph α).cliqueSet n = ∅ :=
  (cliqueFree_bot hn).cliqueSet
#align simple_graph.clique_set_bot SimpleGraph.cliqueSet_bot

@[simp]
theorem cliqueSet_map (hn : n ≠ 1) (G : SimpleGraph α) (f : α ↪ β) :
    (G.map f).cliqueSet n = map f '' G.cliqueSet n := by
  ext s
  constructor
  · rintro ⟨hs, rfl⟩
    have hs' : (s.preimage f f.injective.injOn).map f = s := by
      classical
      rw [map_eq_image, image_preimage, filter_true_of_mem]
      rintro a ha
      obtain ⟨b, hb, hba⟩ := exists_mem_ne (hn.lt_of_le' <| Finset.card_pos.2 ⟨a, ha⟩) a
      obtain ⟨c, _, _, hc, _⟩ := hs ha hb hba.symm
      exact ⟨c, hc⟩
    refine ⟨s.preimage f f.injective.injOn, ⟨?_, by rw [← card_map f, hs']⟩, hs'⟩
    rw [coe_preimage]
    exact fun a ha b hb hab => map_adj_apply.1 (hs ha hb <| f.injective.ne hab)
  · rintro ⟨s, hs, rfl⟩
    exact hs.map
#align simple_graph.clique_set_map SimpleGraph.cliqueSet_map

@[simp]
theorem cliqueSet_map_of_equiv (G : SimpleGraph α) (e : α ≃ β) (n : ℕ) :
    (G.map e.toEmbedding).cliqueSet n = map e.toEmbedding '' G.cliqueSet n := by
  obtain rfl | hn := eq_or_ne n 1
  · ext
    simp [e.exists_congr_left]
  · exact cliqueSet_map hn _ _
#align simple_graph.clique_set_map_of_equiv SimpleGraph.cliqueSet_map_of_equiv

end CliqueSet

/-! ### Finset of cliques -/


section CliqueFinset

variable [Fintype α] [DecidableEq α] [DecidableRel G.Adj] {n : ℕ} {a b c : α} {s : Finset α}

/-- The `n`-cliques in a graph as a finset. -/
def cliqueFinset (n : ℕ) : Finset (Finset α) :=
  univ.filter <| G.IsNClique n
#align simple_graph.clique_finset SimpleGraph.cliqueFinset

variable {G} in
@[simp]
theorem mem_cliqueFinset_iff : s ∈ G.cliqueFinset n ↔ G.IsNClique n s :=
  mem_filter.trans <| and_iff_right <| mem_univ _
#align simple_graph.mem_clique_finset_iff SimpleGraph.mem_cliqueFinset_iff

@[simp, norm_cast]
theorem coe_cliqueFinset (n : ℕ) : (G.cliqueFinset n : Set (Finset α)) = G.cliqueSet n :=
  Set.ext fun _ ↦ mem_cliqueFinset_iff
#align simple_graph.coe_clique_finset SimpleGraph.coe_cliqueFinset

variable {G}

@[simp]
theorem cliqueFinset_eq_empty_iff : G.cliqueFinset n = ∅ ↔ G.CliqueFree n := by
  simp_rw [CliqueFree, eq_empty_iff_forall_not_mem, mem_cliqueFinset_iff]
#align simple_graph.clique_finset_eq_empty_iff SimpleGraph.cliqueFinset_eq_empty_iff

protected alias ⟨_, CliqueFree.cliqueFinset⟩ := cliqueFinset_eq_empty_iff
#align simple_graph.clique_free.clique_finset SimpleGraph.CliqueFree.cliqueFinset

theorem card_cliqueFinset_le : (G.cliqueFinset n).card ≤ (card α).choose n := by
  rw [← card_univ, ← card_powersetCard]
  refine card_mono fun s => ?_
  simpa [mem_powersetCard_univ] using IsNClique.card_eq
#align simple_graph.card_clique_finset_le SimpleGraph.card_cliqueFinset_le

variable [DecidableRel H.Adj]

@[mono]
theorem cliqueFinset_mono (h : G ≤ H) : G.cliqueFinset n ⊆ H.cliqueFinset n :=
  monotone_filter_right _ fun _ ↦ IsNClique.mono h
#align simple_graph.clique_finset_mono SimpleGraph.cliqueFinset_mono

variable [Fintype β] [DecidableEq β] (G)

@[simp]
theorem cliqueFinset_map (f : α ↪ β) (hn : n ≠ 1) :
    (G.map f).cliqueFinset n = (G.cliqueFinset n).map ⟨map f, Finset.map_injective _⟩ :=
  coe_injective <| by
    simp_rw [coe_cliqueFinset, cliqueSet_map hn, coe_map, coe_cliqueFinset, Embedding.coeFn_mk]
#align simple_graph.clique_finset_map SimpleGraph.cliqueFinset_map

@[simp]
theorem cliqueFinset_map_of_equiv (e : α ≃ β) (n : ℕ) :
    (G.map e.toEmbedding).cliqueFinset n =
      (G.cliqueFinset n).map ⟨map e.toEmbedding, Finset.map_injective _⟩ :=
  coe_injective <| by push_cast; exact cliqueSet_map_of_equiv _ _ _
#align simple_graph.clique_finset_map_of_equiv SimpleGraph.cliqueFinset_map_of_equiv

end CliqueFinset

end SimpleGraph
