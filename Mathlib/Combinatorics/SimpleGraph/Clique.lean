/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.Finset.Pairwise
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Lattice
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Graph cliques

This file defines cliques in simple graphs.
A clique is a set of vertices that are pairwise adjacent.

## Main declarations

* `SimpleGraph.IsClique`: Predicate for a set of vertices to be a clique.
* `SimpleGraph.IsNClique`: Predicate for a set of vertices to be an `n`-clique.
* `SimpleGraph.cliqueFinset`: Finset of `n`-cliques of a graph.
* `SimpleGraph.CliqueFree`: Predicate for a graph to have no `n`-cliques.
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

theorem isClique_iff : G.IsClique s ↔ s.Pairwise G.Adj :=
  Iff.rfl

lemma not_isClique_iff : ¬ G.IsClique s ↔ ∃ (v w : s), v ≠ w ∧ ¬ G.Adj v w := by
  aesop (add simp [isClique_iff, Set.Pairwise])

/-- A clique is a set of vertices whose induced graph is complete. -/
theorem isClique_iff_induce_eq : G.IsClique s ↔ G.induce s = ⊤ := by
  rw [isClique_iff]
  constructor
  · intro h
    ext ⟨v, hv⟩ ⟨w, hw⟩
    simp only [comap_adj, top_adj, Ne, Subtype.mk_eq_mk]
    exact ⟨Adj.ne, h hv hw⟩
  · intro h v hv w hw hne
    have h2 : (G.induce s).Adj ⟨v, hv⟩ ⟨w, hw⟩ = _ := rfl
    conv_lhs at h2 => rw [h]
    simp only [top_adj, ne_eq, Subtype.mk.injEq, eq_iff_iff] at h2
    exact h2.1 hne

instance [DecidableEq α] [DecidableRel G.Adj] {s : Finset α} : Decidable (G.IsClique s) :=
  decidable_of_iff' _ G.isClique_iff

variable {G H} {a b : α}

lemma isClique_empty : G.IsClique ∅ := by simp

lemma isClique_singleton (a : α) : G.IsClique {a} := by simp

theorem IsClique.of_subsingleton {G : SimpleGraph α} (hs : s.Subsingleton) : G.IsClique s :=
  hs.pairwise G.Adj

lemma isClique_pair : G.IsClique {a, b} ↔ a ≠ b → G.Adj a b := Set.pairwise_pair_of_symmetric G.symm

@[simp]
lemma isClique_insert : G.IsClique (insert a s) ↔ G.IsClique s ∧ ∀ b ∈ s, a ≠ b → G.Adj a b :=
  Set.pairwise_insert_of_symmetric G.symm

lemma isClique_insert_of_notMem (ha : a ∉ s) :
    G.IsClique (insert a s) ↔ G.IsClique s ∧ ∀ b ∈ s, G.Adj a b :=
  Set.pairwise_insert_of_symmetric_of_notMem G.symm ha

@[deprecated (since := "2025-05-23")] alias isClique_insert_of_not_mem := isClique_insert_of_notMem

lemma IsClique.insert (hs : G.IsClique s) (h : ∀ b ∈ s, a ≠ b → G.Adj a b) :
    G.IsClique (insert a s) := hs.insert_of_symmetric G.symm h

theorem IsClique.mono (h : G ≤ H) : G.IsClique s → H.IsClique s := Set.Pairwise.mono' h

theorem IsClique.subset (h : t ⊆ s) : G.IsClique s → G.IsClique t := Set.Pairwise.mono h

@[simp]
theorem isClique_bot_iff : (⊥ : SimpleGraph α).IsClique s ↔ (s : Set α).Subsingleton :=
  Set.pairwise_bot_iff

alias ⟨IsClique.subsingleton, _⟩ := isClique_bot_iff

protected theorem IsClique.map (h : G.IsClique s) {f : α ↪ β} : (G.map f).IsClique (f '' s) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
  exact ⟨a, b, h ha hb <| ne_of_apply_ne _ hab, rfl, rfl⟩

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

variable {f : α ↪ β} {t : Finset β}

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
    (G.map f).IsClique t ↔ #t ≤ 1 ∨ ∃ (s : Finset α), G.IsClique s ∧ s.map f = t := by
  obtain (ht | ht) := le_or_gt #t 1
  · simp only [ht, true_or, iff_true]
    exact IsClique.of_subsingleton <| card_le_one.1 ht
  rw [isClique_map_finset_iff_of_nontrivial, ← not_lt]
  · simp [ht]
  exact Finset.one_lt_card_iff_nontrivial.mp ht

protected theorem IsClique.finsetMap {f : α ↪ β} {s : Finset α} (h : G.IsClique s) :
    (G.map f).IsClique (s.map f) := by
  simpa

/-- If a set of vertices `A` is a clique in subgraph of `G` induced by a superset of `A`,
its embedding is a clique in `G`. -/
theorem IsClique.of_induce {S : Subgraph G} {F : Set α} {A : Set F}
    (c : (S.induce F).coe.IsClique A) : G.IsClique (Subtype.val '' A) := by
  simp only [Set.Pairwise, Set.mem_image, Subtype.exists, exists_and_right, exists_eq_right]
  intro _ ⟨_, ainA⟩ _ ⟨_, binA⟩ anb
  exact S.adj_sub (c ainA binA (Subtype.coe_ne_coe.mp anb)).2.2

lemma IsClique.sdiff_of_sup_edge {v w : α} {s : Set α} (hc : (G ⊔ edge v w).IsClique s) :
    G.IsClique (s \ {v}) := by
  intro _ hx _ hy hxy
  have := hc hx.1 hy.1 hxy
  simp_all [sup_adj, edge_adj]

lemma isClique_sup_edge_of_ne_sdiff {v w : α} {s : Set α} (h : v ≠ w) (hv : G.IsClique (s \ {v}))
    (hw : G.IsClique (s \ {w})) : (G ⊔ edge v w).IsClique s := by
  intro x hx y hy hxy
  by_cases h' : x ∈ s \ {v} ∧ y ∈ s \ {v} ∨ x ∈ s \ {w} ∧ y ∈ s \ {w}
  · obtain (⟨hx, hy⟩ | ⟨hx, hy⟩) := h'
    · exact hv.mono le_sup_left hx hy hxy
    · exact hw.mono le_sup_left hx hy hxy
  · exact Or.inr ⟨by by_cases x = v <;> aesop, hxy⟩

lemma isClique_sup_edge_of_ne_iff {v w : α} {s : Set α} (h : v ≠ w) :
    (G ⊔ edge v w).IsClique s ↔ G.IsClique (s \ {v}) ∧ G.IsClique (s \ {w}) :=
  ⟨fun h' ↦ ⟨h'.sdiff_of_sup_edge, (edge_comm .. ▸ h').sdiff_of_sup_edge⟩,
    fun h' ↦ isClique_sup_edge_of_ne_sdiff h h'.1 h'.2⟩

/-- The vertices in a copy of `⊤` are a clique. -/
theorem isClique_range_copy_top (f : Copy (⊤ : SimpleGraph β) G) :
    G.IsClique (Set.range f) := by
  intro _ ⟨_, h⟩ _ ⟨_, h'⟩ nh
  rw [← h, ← Copy.topEmbedding_apply, ← h', ← Copy.topEmbedding_apply] at nh ⊢
  rwa [← f.topEmbedding.coe_toEmbedding, (f.topEmbedding.apply_eq_iff_eq _ _).ne,
    ← top_adj, ← f.topEmbedding.map_adj_iff] at nh

end Clique

/-! ### `n`-cliques -/


section NClique

variable {n : ℕ} {s : Finset α}

/-- An `n`-clique in a graph is a set of `n` vertices which are pairwise connected. -/
structure IsNClique (n : ℕ) (s : Finset α) : Prop where
  isClique : G.IsClique s
  card_eq : #s = n

theorem isNClique_iff : G.IsNClique n s ↔ G.IsClique s ∧ #s = n :=
  ⟨fun h ↦ ⟨h.1, h.2⟩, fun h ↦ ⟨h.1, h.2⟩⟩

instance [DecidableEq α] [DecidableRel G.Adj] {n : ℕ} {s : Finset α} :
    Decidable (G.IsNClique n s) :=
  decidable_of_iff' _ G.isNClique_iff

variable {G H} {a b c : α}

@[simp] lemma isNClique_empty : G.IsNClique n ∅ ↔ n = 0 := by simp [isNClique_iff, eq_comm]

@[simp]
lemma isNClique_singleton : G.IsNClique n {a} ↔ n = 1 := by simp [isNClique_iff, eq_comm]

theorem IsNClique.mono (h : G ≤ H) : G.IsNClique n s → H.IsNClique n s := by
  simp_rw [isNClique_iff]
  exact And.imp_left (IsClique.mono h)

protected theorem IsNClique.map (h : G.IsNClique n s) {f : α ↪ β} :
    (G.map f).IsNClique n (s.map f) :=
  ⟨by rw [coe_map]; exact h.1.map, (card_map _).trans h.2⟩

theorem isNClique_map_iff (hn : 1 < n) {t : Finset β} {f : α ↪ β} :
    (G.map f).IsNClique n t ↔ ∃ s : Finset α, G.IsNClique n s ∧ s.map f = t := by
  rw [isNClique_iff, isClique_map_finset_iff, or_and_right,
    or_iff_right (by rintro ⟨h', rfl⟩; exact h'.not_gt hn)]
  constructor
  · rintro ⟨⟨s, hs, rfl⟩, rfl⟩
    simp [isNClique_iff, hs]
  rintro ⟨s, hs, rfl⟩
  simp [hs.card_eq, hs.isClique]

@[simp]
theorem isNClique_bot_iff : (⊥ : SimpleGraph α).IsNClique n s ↔ n ≤ 1 ∧ #s = n := by
  rw [isNClique_iff, isClique_bot_iff]
  refine and_congr_left ?_
  rintro rfl
  exact card_le_one.symm

@[simp]
theorem isNClique_zero : G.IsNClique 0 s ↔ s = ∅ := by
  simp only [isNClique_iff, Finset.card_eq_zero, and_iff_right_iff_imp]; rintro rfl; simp

@[simp]
theorem isNClique_one : G.IsNClique 1 s ↔ ∃ a, s = {a} := by
  simp only [isNClique_iff, card_eq_one, and_iff_right_iff_imp]; rintro ⟨a, rfl⟩; simp

section DecidableEq

variable [DecidableEq α]

protected theorem IsNClique.insert (hs : G.IsNClique n s) (h : ∀ b ∈ s, G.Adj a b) :
    G.IsNClique (n + 1) (insert a s) := by
  constructor
  · push_cast
    exact hs.1.insert fun b hb _ => h _ hb
  · rw [card_insert_of_notMem fun ha => (h _ ha).ne rfl, hs.2]

lemma IsNClique.erase_of_mem (hs : G.IsNClique n s) (ha : a ∈ s) :
    G.IsNClique (n - 1) (s.erase a) where
  isClique := hs.isClique.subset <| by simp
  card_eq := by rw [card_erase_of_mem ha, hs.2]

protected lemma IsNClique.insert_erase
    (hs : G.IsNClique n s) (ha : ∀ w ∈ s \ {b}, G.Adj a w) (hb : b ∈ s) :
    G.IsNClique n (insert a (erase s b)) := by
  cases n with
  | zero => exact False.elim <| notMem_empty _ (isNClique_zero.1 hs ▸ hb)
  | succ _ => exact (hs.erase_of_mem hb).insert fun w h ↦ by aesop

theorem is3Clique_triple_iff : G.IsNClique 3 {a, b, c} ↔ G.Adj a b ∧ G.Adj a c ∧ G.Adj b c := by
  simp only [isNClique_iff, Set.pairwise_insert_of_symmetric G.symm, coe_insert]
  by_cases hab : a = b <;> by_cases hbc : b = c <;> by_cases hac : a = c <;> subst_vars <;>
    simp [and_rotate, *]

theorem is3Clique_iff :
    G.IsNClique 3 s ↔ ∃ a b c, G.Adj a b ∧ G.Adj a c ∧ G.Adj b c ∧ s = {a, b, c} := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨a, b, c, -, -, -, hs⟩ := card_eq_three.1 h.card_eq
    refine ⟨a, b, c, ?_⟩
    rwa [hs, eq_self_iff_true, and_true, is3Clique_triple_iff.symm, ← hs]
  · rintro ⟨a, b, c, hab, hbc, hca, rfl⟩
    exact is3Clique_triple_iff.2 ⟨hab, hbc, hca⟩

end DecidableEq

theorem is3Clique_iff_exists_cycle_length_three :
    (∃ s : Finset α, G.IsNClique 3 s) ↔ ∃ (u : α) (w : G.Walk u u), w.IsCycle ∧ w.length = 3 := by
  classical
  simp_rw [is3Clique_iff, isCycle_def]
  exact
    ⟨(fun ⟨_, a, _, _, hab, hac, hbc, _⟩ => ⟨a, cons hab (cons hbc (cons hac.symm nil)), by aesop⟩),
    (fun ⟨_, .cons hab (.cons hbc (.cons hca nil)), _, _⟩ => ⟨_, _, _, _, hab, hca.symm, hbc, rfl⟩)⟩

/-- If a set of vertices `A` is an `n`-clique in subgraph of `G` induced by a superset of `A`,
its embedding is an `n`-clique in `G`. -/
theorem IsNClique.of_induce {S : Subgraph G} {F : Set α} {s : Finset { x // x ∈ F }} {n : ℕ}
    (cc : (S.induce F).coe.IsNClique n s) :
    G.IsNClique n (Finset.map ⟨Subtype.val, Subtype.val_injective⟩ s) := by
  rw [isNClique_iff] at cc ⊢
  simp only [coe_map, card_map]
  exact ⟨cc.left.of_induce, cc.right⟩

lemma IsNClique.erase_of_sup_edge_of_mem [DecidableEq α] {v w : α} {s : Finset α} {n : ℕ}
    (hc : (G ⊔ edge v w).IsNClique n s) (hx : v ∈ s) : G.IsNClique (n - 1) (s.erase v) where
  isClique := coe_erase v _ ▸ hc.1.sdiff_of_sup_edge
  card_eq  := by rw [card_erase_of_mem hx, hc.2]

/-- The vertices in a copy of `⊤ : SimpleGraph β` are a `card β`-clique. -/
theorem isNClique_map_copy_top [Fintype β] (f : Copy (⊤ : SimpleGraph β) G) :
    G.IsNClique (card β) (univ.map f.toEmbedding) := by
  rw [isNClique_iff, card_map, card_univ, coe_map, coe_univ, Set.image_univ]
  exact ⟨isClique_range_copy_top f, rfl⟩

end NClique

/-! ### Graphs without cliques -/


section CliqueFree

variable {m n : ℕ}

/-- `G.CliqueFree n` means that `G` has no `n`-cliques. -/
def CliqueFree (n : ℕ) : Prop :=
  ∀ t, ¬G.IsNClique n t

variable {G H} {s : Finset α}

theorem IsNClique.not_cliqueFree (hG : G.IsNClique n s) : ¬G.CliqueFree n :=
  fun h ↦ h _ hG

theorem not_cliqueFree_of_top_embedding {n : ℕ} (f : (⊤ : SimpleGraph (Fin n)) ↪g G) :
    ¬G.CliqueFree n := by
  simp only [CliqueFree, isNClique_iff, isClique_iff_induce_eq, not_forall, Classical.not_not]
  use Finset.univ.map f.toEmbedding
  simp only [card_map, Finset.card_fin, and_true]
  ext ⟨v, hv⟩ ⟨w, hw⟩
  simp only [coe_map, Set.mem_image, coe_univ, Set.mem_univ, true_and] at hv hw
  obtain ⟨v', rfl⟩ := hv
  obtain ⟨w', rfl⟩ := hw
  simp_rw [RelEmbedding.coe_toEmbedding, comap_adj, Function.Embedding.coe_subtype, f.map_adj_iff,
    top_adj, ne_eq, Subtype.mk.injEq, RelEmbedding.inj]

/-- An embedding of a complete graph that witnesses the fact that the graph is not clique-free. -/
noncomputable def topEmbeddingOfNotCliqueFree {n : ℕ} (h : ¬G.CliqueFree n) :
    (⊤ : SimpleGraph (Fin n)) ↪g G := by
  simp only [CliqueFree, isNClique_iff, isClique_iff_induce_eq, not_forall, Classical.not_not] at h
  obtain ⟨ha, hb⟩ := h.choose_spec
  have : (⊤ : SimpleGraph (Fin #h.choose)) ≃g (⊤ : SimpleGraph h.choose) := by
    apply Iso.completeGraph
    simpa using (Fintype.equivFin h.choose).symm
  rw [← ha] at this
  convert (Embedding.induce ↑h.choose.toSet).comp this.toEmbedding
  exact hb.symm
 
theorem not_cliqueFree_iff (n : ℕ) : ¬G.CliqueFree n ↔ Nonempty (completeGraph (Fin n) ↪g G) :=
  ⟨fun h ↦ ⟨topEmbeddingOfNotCliqueFree h⟩, fun ⟨f⟩ ↦ not_cliqueFree_of_top_embedding f⟩

theorem cliqueFree_iff {n : ℕ} : G.CliqueFree n ↔ IsEmpty (completeGraph (Fin n) ↪g G) := by
  rw [← not_iff_not, not_cliqueFree_iff, not_isEmpty_iff]

/-- A simple graph has no `card β`-cliques iff it does not contain `⊤ : SimpleGraph β`. -/
theorem cliqueFree_iff_top_free {β : Type*} [Fintype β] :
    G.CliqueFree (card β) ↔ (⊤ : SimpleGraph β).Free G := by
  rw [← not_iff_not, not_free, not_cliqueFree_iff,
    isContained_congr (Iso.completeGraph (Fintype.equivFin β)) Iso.refl]
  exact ⟨fun ⟨f⟩ ↦ ⟨f.toCopy⟩, fun ⟨f⟩ ↦ ⟨f.topEmbedding⟩⟩

theorem not_cliqueFree_card_of_top_embedding [Fintype α] (f : (⊤ : SimpleGraph α) ↪g G) :
    ¬G.CliqueFree (card α) := by
  rw [not_cliqueFree_iff]
  exact ⟨(Iso.completeGraph (Fintype.equivFin α)).symm.toEmbedding.trans f⟩

@[simp] lemma not_cliqueFree_zero : ¬ G.CliqueFree 0 :=
  fun h ↦ h ∅ <| isNClique_empty.mpr rfl

@[simp]
theorem cliqueFree_bot (h : 2 ≤ n) : (⊥ : SimpleGraph α).CliqueFree n := by
  intro t ht
  have := le_trans h (isNClique_bot_iff.1 ht).1
  contradiction

theorem CliqueFree.mono (h : m ≤ n) : G.CliqueFree m → G.CliqueFree n := by
  intro hG s hs
  obtain ⟨t, hts, ht⟩ := exists_subset_card_eq (h.trans hs.card_eq.ge)
  exact hG _ ⟨hs.isClique.subset hts, ht⟩

theorem CliqueFree.anti (h : G ≤ H) : H.CliqueFree n → G.CliqueFree n :=
  forall_imp fun _ ↦ mt <| IsNClique.mono h

/-- If a graph is cliquefree, any graph that embeds into it is also cliquefree. -/
theorem CliqueFree.comap {H : SimpleGraph β} (f : H ↪g G) : G.CliqueFree n → H.CliqueFree n := by
  intro h; contrapose h
  exact not_cliqueFree_of_top_embedding <| f.comp (topEmbeddingOfNotCliqueFree h)

@[simp] theorem cliqueFree_map_iff {f : α ↪ β} [Nonempty α] :
    (G.map f).CliqueFree n ↔ G.CliqueFree n := by
  obtain (hle | hlt) := le_or_gt n 1
  · obtain (rfl | rfl) := Nat.le_one_iff_eq_zero_or_eq_one.1 hle
    · simp [CliqueFree]
    simp [CliqueFree, show ∃ (_ : β), True from ⟨f (Classical.arbitrary _), trivial⟩]
  simp [CliqueFree, isNClique_map_iff hlt]

/-- See `SimpleGraph.cliqueFree_of_chromaticNumber_lt` for a tighter bound. -/
theorem cliqueFree_of_card_lt [Fintype α] (hc : card α < n) : G.CliqueFree n := by
  rw [cliqueFree_iff]
  contrapose! hc
  simpa only [Fintype.card_fin] using Fintype.card_le_of_embedding hc.some.toEmbedding

/-- A complete `r`-partite graph has no `n`-cliques for `r < n`. -/
theorem cliqueFree_completeMultipartiteGraph {ι : Type*} [Fintype ι] (V : ι → Type*)
    (hc : card ι < n) : (completeMultipartiteGraph V).CliqueFree n := by
  rw [cliqueFree_iff, isEmpty_iff]
  intro f
  obtain ⟨v, w, hn, he⟩ := exists_ne_map_eq_of_card_lt (Sigma.fst ∘ f) (by simp [hc])
  rw [← top_adj, ← f.map_adj_iff, comap_adj, top_adj] at hn
  exact absurd he hn

namespace completeMultipartiteGraph

variable {ι : Type*} (V : ι → Type*)

/-- Embedding of the complete graph on `ι` into `completeMultipartiteGraph` on `ι` nonempty parts -/
@[simps]
def topEmbedding (f : ∀ (i : ι), V i) :
    (⊤ : SimpleGraph ι) ↪g completeMultipartiteGraph V where
  toFun := fun i ↦ ⟨i, f i⟩
  inj' := fun _ _ h ↦ (Sigma.mk.inj_iff.1 h).1
  map_rel_iff' := by simp

theorem not_cliqueFree_of_le_card [Fintype ι] (f : ∀ (i : ι), V i) (hc : n ≤ Fintype.card ι) :
    ¬ (completeMultipartiteGraph V).CliqueFree n :=
  fun hf ↦ (cliqueFree_iff.1 <| hf.mono hc).elim' <|
    (topEmbedding V f).comp (Iso.completeGraph (Fintype.equivFin ι).symm).toEmbedding

theorem not_cliqueFree_of_infinite [Infinite ι] (f : ∀ (i : ι), V i) :
    ¬ (completeMultipartiteGraph V).CliqueFree n :=
  fun hf ↦ not_cliqueFree_of_top_embedding (topEmbedding V f |>.comp
            <| Embedding.completeGraph <| Fin.valEmbedding.trans <| Infinite.natEmbedding ι) hf

theorem not_cliqueFree_of_le_enatCard (f : ∀ (i : ι), V i) (hc : n ≤ ENat.card ι) :
    ¬ (completeMultipartiteGraph V).CliqueFree n := by
  by_cases h : Infinite ι
  · exact not_cliqueFree_of_infinite V f
  · have : Fintype ι := fintypeOfNotInfinite h
    rw [ENat.card_eq_coe_fintype_card, Nat.cast_le] at hc
    exact not_cliqueFree_of_le_card V f hc

end completeMultipartiteGraph

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
lemma cliqueFree_one : G.CliqueFree 1 ↔ IsEmpty α := by
  simp [CliqueFree, isEmpty_iff]

@[simp]
theorem cliqueFree_two : G.CliqueFree 2 ↔ G = ⊥ := by
  classical
  constructor
  · simp_rw [← edgeSet_eq_empty, Set.eq_empty_iff_forall_notMem, Sym2.forall, mem_edgeSet]
    exact fun h a b hab => h _ ⟨by simpa [hab.ne], card_pair hab.ne⟩
  · rintro rfl
    exact cliqueFree_bot le_rfl

lemma CliqueFree.mem_of_sup_edge_isNClique {x y : α} {t : Finset α} {n : ℕ} (h : G.CliqueFree n)
    (hc : (G ⊔ edge x y).IsNClique n t) : x ∈ t := by
  by_contra! hf
  have ht : (t : Set α) \ {x} = t := sdiff_eq_left.mpr <| Set.disjoint_singleton_right.mpr hf
  exact h t ⟨ht ▸ hc.1.sdiff_of_sup_edge, hc.2⟩

open Classical in
/-- Adding an edge increases the clique number by at most one. -/
protected theorem CliqueFree.sup_edge (h : G.CliqueFree n) (v w : α) :
    (G ⊔ edge v w).CliqueFree (n + 1) :=
  fun _ hs ↦ (hs.erase_of_sup_edge_of_mem <|
    (h.mono n.le_succ).mem_of_sup_edge_isNClique hs).not_cliqueFree h

lemma IsNClique.exists_not_adj_of_cliqueFree_succ (hc : G.IsNClique n s)
    (h : G.CliqueFree (n + 1)) (x : α) : ∃ y, y ∈ s ∧ ¬ G.Adj x y := by
  classical
  by_contra! hf
  exact (hc.insert hf).not_cliqueFree h

lemma exists_of_maximal_cliqueFree_not_adj [DecidableEq α]
    (h : Maximal (fun H ↦ H.CliqueFree (n + 1)) G) {x y : α} (hne : x ≠ y) (hn : ¬ G.Adj x y) :
    ∃ s, x ∉ s ∧ y ∉ s ∧ G.IsNClique n (insert x s) ∧ G.IsNClique n (insert y s) := by
  obtain ⟨t, hc⟩ := not_forall_not.1 <| h.not_prop_of_gt <| G.lt_sup_edge _ _ hne hn
  use (t.erase x).erase y, erase_right_comm (a := x) ▸ (notMem_erase _ _), notMem_erase _ _
  have h1 := h.1.mem_of_sup_edge_isNClique hc
  have h2 := h.1.mem_of_sup_edge_isNClique (edge_comm .. ▸ hc)
  rw [insert_erase <| mem_erase_of_ne_of_mem hne.symm h2, erase_right_comm,
      insert_erase <| mem_erase_of_ne_of_mem hne h1]
  exact ⟨(edge_comm .. ▸ hc).erase_of_sup_edge_of_mem h2, hc.erase_of_sup_edge_of_mem h1⟩

end CliqueFree

section CliqueFreeOn
variable {s s₁ s₂ : Set α} {a : α} {m n : ℕ}

/-- `G.CliqueFreeOn s n` means that `G` has no `n`-cliques contained in `s`. -/
def CliqueFreeOn (G : SimpleGraph α) (s : Set α) (n : ℕ) : Prop :=
  ∀ ⦃t⦄, ↑t ⊆ s → ¬G.IsNClique n t

theorem CliqueFreeOn.subset (hs : s₁ ⊆ s₂) (h₂ : G.CliqueFreeOn s₂ n) : G.CliqueFreeOn s₁ n :=
  fun _t hts => h₂ <| hts.trans hs

theorem CliqueFreeOn.mono (hmn : m ≤ n) (hG : G.CliqueFreeOn s m) : G.CliqueFreeOn s n := by
  rintro t hts ht
  obtain ⟨u, hut, hu⟩ := exists_subset_card_eq (hmn.trans ht.card_eq.ge)
  exact hG ((coe_subset.2 hut).trans hts) ⟨ht.isClique.subset hut, hu⟩

theorem CliqueFreeOn.anti (hGH : G ≤ H) (hH : H.CliqueFreeOn s n) : G.CliqueFreeOn s n :=
  fun _t hts ht => hH hts <| ht.mono hGH

@[simp]
theorem cliqueFreeOn_empty : G.CliqueFreeOn ∅ n ↔ n ≠ 0 := by
  simp [CliqueFreeOn, Set.subset_empty_iff]

@[simp]
theorem cliqueFreeOn_singleton : G.CliqueFreeOn {a} n ↔ 1 < n := by
  obtain _ | _ | n := n <;>
    simp [CliqueFreeOn, isNClique_iff, ← subset_singleton_iff', (Nat.succ_ne_zero _).symm]

@[simp]
theorem cliqueFreeOn_univ : G.CliqueFreeOn Set.univ n ↔ G.CliqueFree n := by
  simp [CliqueFree, CliqueFreeOn]

protected theorem CliqueFree.cliqueFreeOn (hG : G.CliqueFree n) : G.CliqueFreeOn s n :=
  fun _t _ ↦ hG _

theorem cliqueFreeOn_of_card_lt {s : Finset α} (h : #s < n) : G.CliqueFreeOn s n :=
  fun _t hts ht => h.not_ge <| ht.2.symm.trans_le <| card_mono hts

-- TODO: Restate using `SimpleGraph.IndepSet` once we have it
@[simp]
theorem cliqueFreeOn_two : G.CliqueFreeOn s 2 ↔ s.Pairwise (G.Adjᶜ) := by
  classical
  refine ⟨fun h a ha b hb _ hab => h ?_ ⟨by simpa [hab.ne], card_pair hab.ne⟩, ?_⟩
  · push_cast
    exact Set.insert_subset_iff.2 ⟨ha, Set.singleton_subset_iff.2 hb⟩
  simp only [CliqueFreeOn, isNClique_iff, card_eq_two, not_and, not_exists]
  rintro h t hst ht a b hab rfl
  simp only [coe_insert, coe_singleton, Set.insert_subset_iff, Set.singleton_subset_iff] at hst
  refine h hst.1 hst.2 hab (ht ?_ ?_ hab) <;> simp

theorem CliqueFreeOn.of_succ (hs : G.CliqueFreeOn s (n + 1)) (ha : a ∈ s) :
    G.CliqueFreeOn (s ∩ G.neighborSet a) n := by
  classical
  refine fun t hts ht => hs ?_ (ht.insert fun b hb => (hts hb).2)
  push_cast
  exact Set.insert_subset_iff.2 ⟨ha, hts.trans Set.inter_subset_left⟩

end CliqueFreeOn

/-! ### Set of cliques -/


section CliqueSet

variable {n : ℕ} {s : Finset α}

/-- The `n`-cliques in a graph as a set. -/
def cliqueSet (n : ℕ) : Set (Finset α) :=
  { s | G.IsNClique n s }

variable {G H}

@[simp]
theorem mem_cliqueSet_iff : s ∈ G.cliqueSet n ↔ G.IsNClique n s :=
  Iff.rfl

@[simp]
theorem cliqueSet_eq_empty_iff : G.cliqueSet n = ∅ ↔ G.CliqueFree n := by
  simp_rw [CliqueFree, Set.eq_empty_iff_forall_notMem, mem_cliqueSet_iff]

protected alias ⟨_, CliqueFree.cliqueSet⟩ := cliqueSet_eq_empty_iff

@[gcongr, mono]
theorem cliqueSet_mono (h : G ≤ H) : G.cliqueSet n ⊆ H.cliqueSet n :=
  fun _ ↦ IsNClique.mono h

theorem cliqueSet_mono' (h : G ≤ H) : G.cliqueSet ≤ H.cliqueSet :=
  fun _ ↦ cliqueSet_mono h

@[simp]
theorem cliqueSet_zero (G : SimpleGraph α) : G.cliqueSet 0 = {∅} := Set.ext fun s => by simp

@[simp]
theorem cliqueSet_one (G : SimpleGraph α) : G.cliqueSet 1 = Set.range singleton :=
  Set.ext fun s => by simp [eq_comm]

@[simp]
theorem cliqueSet_bot (hn : 1 < n) : (⊥ : SimpleGraph α).cliqueSet n = ∅ :=
  (cliqueFree_bot hn).cliqueSet

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

@[simp]
theorem cliqueSet_map_of_equiv (G : SimpleGraph α) (e : α ≃ β) (n : ℕ) :
    (G.map e.toEmbedding).cliqueSet n = map e.toEmbedding '' G.cliqueSet n := by
  obtain rfl | hn := eq_or_ne n 1
  · ext
    simp [e.exists_congr_left]
  · exact cliqueSet_map hn _ _

end CliqueSet

/-! ### Clique number -/


section CliqueNumber

variable {α : Type*} {G : SimpleGraph α}

/-- The maximum number of vertices in a clique of a graph `G`. -/
noncomputable def cliqueNum (G : SimpleGraph α) : ℕ := sSup {n | ∃ s, G.IsNClique n s}

private lemma fintype_cliqueNum_bddAbove [Fintype α] : BddAbove {n | ∃ s, G.IsNClique n s} := by
  use Fintype.card α
  rintro y ⟨s, syc⟩
  rw [isNClique_iff] at syc
  rw [← syc.right]
  exact Finset.card_le_card (Finset.subset_univ s)

lemma IsClique.card_le_cliqueNum [Finite α] {t : Finset α} {tc : G.IsClique t} :
    #t ≤ G.cliqueNum := by
  cases nonempty_fintype α
  exact le_csSup G.fintype_cliqueNum_bddAbove (Exists.intro t ⟨tc, rfl⟩)

lemma exists_isNClique_cliqueNum [Finite α] : ∃ s, G.IsNClique G.cliqueNum s := by
  cases nonempty_fintype α
  exact Nat.sSup_mem ⟨0, by simp⟩ G.fintype_cliqueNum_bddAbove

/-- A maximum clique in a graph `G` is a clique with the largest possible size. -/
structure IsMaximumClique [Fintype α] (G : SimpleGraph α) (s : Finset α) : Prop where
  (isClique : G.IsClique s)
  (maximum : ∀ t : Finset α, G.IsClique t → #t ≤ #s)

theorem isMaximumClique_iff [Fintype α] {s : Finset α} :
    G.IsMaximumClique s ↔ G.IsClique s ∧ ∀ t : Finset α, G.IsClique t → #t ≤ #s :=
  ⟨fun h ↦ ⟨h.1, h.2⟩, fun h ↦ ⟨h.1, h.2⟩⟩

/-- A maximal clique in a graph `G` is a clique that cannot be extended by adding more vertices. -/
theorem isMaximalClique_iff {s : Set α} :
    Maximal G.IsClique s ↔ G.IsClique s ∧ ∀ t : Set α, G.IsClique t → s ⊆ t → t ⊆ s :=
  Iff.rfl

lemma IsMaximumClique.isMaximalClique [Fintype α] (s : Finset α) (M : G.IsMaximumClique s) :
    Maximal G.IsClique s :=
  ⟨ M.isClique,
    fun t ht hsub => by
      by_contra hc
      have fint : Fintype t := ofFinite ↑t
      have ne : s ≠ t.toFinset := fun a ↦ by subst a; simp_all[Set.coe_toFinset, not_true_eq_false]
      have hle : #t.toFinset ≤ #s := M.maximum t.toFinset (by simp [Set.coe_toFinset, ht])
      have hlt : #s < #t.toFinset :=
        card_lt_card (ssubset_of_ne_of_subset ne (Set.subset_toFinset.mpr hsub))
      exact lt_irrefl _ (lt_of_lt_of_le hlt hle) ⟩

lemma maximumClique_card_eq_cliqueNum [Fintype α] (s : Finset α) (sm : G.IsMaximumClique s) :
    #s = G.cliqueNum := by
  obtain ⟨sc, sm⟩ := sm
  obtain ⟨t, tc, tcard⟩ := G.exists_isNClique_cliqueNum
  exact eq_of_le_of_not_lt sc.card_le_cliqueNum (by simp [← tcard, sm t tc])

lemma maximumClique_exists [Fintype α] : ∃ (s : Finset α), G.IsMaximumClique s := by
  obtain ⟨s, snc⟩ := G.exists_isNClique_cliqueNum
  exact ⟨s, ⟨snc.isClique, fun t ht => snc.card_eq.symm ▸ ht.card_le_cliqueNum⟩⟩

end CliqueNumber

/-! ### Finset of cliques -/


section CliqueFinset

variable [Fintype α] [DecidableEq α] [DecidableRel G.Adj] {n : ℕ} {s : Finset α}

/-- The `n`-cliques in a graph as a finset. -/
def cliqueFinset (n : ℕ) : Finset (Finset α) := {s | G.IsNClique n s}

variable {G} in
@[simp]
theorem mem_cliqueFinset_iff : s ∈ G.cliqueFinset n ↔ G.IsNClique n s :=
  mem_filter.trans <| and_iff_right <| mem_univ _

@[simp, norm_cast]
theorem coe_cliqueFinset (n : ℕ) : (G.cliqueFinset n : Set (Finset α)) = G.cliqueSet n :=
  Set.ext fun _ ↦ mem_cliqueFinset_iff

variable {G}

@[simp]
theorem cliqueFinset_eq_empty_iff : G.cliqueFinset n = ∅ ↔ G.CliqueFree n := by
  simp_rw [CliqueFree, eq_empty_iff_forall_notMem, mem_cliqueFinset_iff]

protected alias ⟨_, CliqueFree.cliqueFinset⟩ := cliqueFinset_eq_empty_iff

theorem card_cliqueFinset_le : #(G.cliqueFinset n) ≤ (card α).choose n := by
  rw [← card_univ, ← card_powersetCard]
  refine card_mono fun s => ?_
  simpa [mem_powersetCard_univ] using IsNClique.card_eq

variable [DecidableRel H.Adj]

@[gcongr, mono]
theorem cliqueFinset_mono (h : G ≤ H) : G.cliqueFinset n ⊆ H.cliqueFinset n :=
  monotone_filter_right _ fun _ _ ↦ IsNClique.mono h

variable [Fintype β] [DecidableEq β] (G)

@[simp]
theorem cliqueFinset_map (f : α ↪ β) (hn : n ≠ 1) :
    (G.map f).cliqueFinset n = (G.cliqueFinset n).map ⟨map f, Finset.map_injective _⟩ :=
  coe_injective <| by
    simp_rw [coe_cliqueFinset, cliqueSet_map hn, coe_map, coe_cliqueFinset, Embedding.coeFn_mk]

@[simp]
theorem cliqueFinset_map_of_equiv (e : α ≃ β) (n : ℕ) :
    (G.map e.toEmbedding).cliqueFinset n =
      (G.cliqueFinset n).map ⟨map e.toEmbedding, Finset.map_injective _⟩ :=
  coe_injective <| by push_cast; exact cliqueSet_map_of_equiv _ _ _

end CliqueFinset

/-! ### Independent Sets -/

section IndepSet

variable {s : Set α}

/-- An independent set in a graph is a set of vertices that are pairwise not adjacent. -/
abbrev IsIndepSet (s : Set α) : Prop :=
  s.Pairwise (fun v w ↦ ¬G.Adj v w)

theorem isIndepSet_iff : G.IsIndepSet s ↔ s.Pairwise (fun v w ↦ ¬G.Adj v w) :=
  Iff.rfl

/-- An independent set is a clique in the complement graph and vice versa. -/
@[simp] theorem isClique_compl : Gᶜ.IsClique s ↔ G.IsIndepSet s := by
  rw [isIndepSet_iff, isClique_iff]; repeat rw [Set.Pairwise]
  simp_all [compl_adj]

/-- An independent set in the complement graph is a clique and vice versa. -/
@[simp] theorem isIndepSet_compl : Gᶜ.IsIndepSet s ↔ G.IsClique s := by
  rw [isIndepSet_iff, isClique_iff]; repeat rw [Set.Pairwise]
  simp_all [compl_adj]

instance [DecidableEq α] [DecidableRel G.Adj] {s : Finset α} : Decidable (G.IsIndepSet s) :=
  decidable_of_iff' _ G.isIndepSet_iff

/-- If `s` is an independent set, its complement meets every edge of `G`. -/
lemma IsIndepSet.nonempty_mem_compl_mem_edge
    [Fintype α] [DecidableEq α] {s : Finset α} (indA : G.IsIndepSet s) {e} (he : e ∈ G.edgeSet) :
    { b ∈ sᶜ | b ∈ e }.Nonempty := by
  obtain ⟨v, w⟩ := e
  by_contra c
  rw [IsIndepSet] at indA
  rw [mem_edgeSet] at he
  rw [not_nonempty_iff_eq_empty, filter_eq_empty_iff] at c
  simp_rw [mem_compl, Sym2.mem_iff, not_or] at c
  by_cases vins : v ∈ s
  · have wins : w ∈ s := by by_contra wnins; exact (c wnins).right rfl
    exact (indA vins wins (Adj.ne he)) he
  · exact (c vins).left rfl

/-- The neighbors of a vertex `v` form an independent set in a triangle free graph `G`. -/
theorem isIndepSet_neighborSet_of_triangleFree (h : G.CliqueFree 3) (v : α) :
    G.IsIndepSet (G.neighborSet v) := by
  classical
  by_contra nind
  rw [IsIndepSet, Set.Pairwise] at nind
  push_neg at nind
  simp_rw [mem_neighborSet] at nind
  obtain ⟨j, avj, k, avk, _, ajk⟩ := nind
  exact h {v, j, k} (is3Clique_triple_iff.mpr (by simp [avj, avk, ajk]))

/-- The embedding of an independent set of an induced subgraph of the subgraph `G` is an independent
set in `G` and vice versa. -/
theorem isIndepSet_induce {F : Set α} {s : Set F} :
    ((⊤ : Subgraph G).induce F).coe.IsIndepSet s ↔ G.IsIndepSet (Subtype.val '' s) := by
  simp [Set.Pairwise]

end IndepSet

/-! ### N-Independent sets -/


section NIndepSet

variable {n : ℕ} {s : Finset α}

/-- An `n`-independent set in a graph is a set of `n` vertices which are pairwise nonadjacent. -/
@[mk_iff]
structure IsNIndepSet (n : ℕ) (s : Finset α) : Prop where
  isIndepSet : G.IsIndepSet s
  card_eq : s.card = n

/-- An `n`-independent set is an `n`-clique in the complement graph and vice versa. -/
@[simp] theorem isNClique_compl : Gᶜ.IsNClique n s ↔ G.IsNIndepSet n s := by
  rw [isNIndepSet_iff]
  simp [isNClique_iff]

/-- An `n`-independent set in the complement graph is an `n`-clique and vice versa. -/
@[simp] theorem isNIndepSet_compl : Gᶜ.IsNIndepSet n s ↔ G.IsNClique n s := by
  rw [isNClique_iff]
  simp [isNIndepSet_iff]

instance [DecidableEq α] [DecidableRel G.Adj] {n : ℕ} {s : Finset α} :
    Decidable (G.IsNIndepSet n s) :=
  decidable_of_iff' _ (G.isNIndepSet_iff n s)

/-- The embedding of an `n`-independent set of an induced subgraph of the subgraph `G` is an
`n`-independent set in `G` and vice versa. -/
theorem isNIndepSet_induce {F : Set α} {s : Finset { x // x ∈ F }} {n : ℕ} :
    ((⊤ : Subgraph G).induce F).coe.IsNIndepSet n ↑s ↔
    G.IsNIndepSet n (Finset.map ⟨Subtype.val, Subtype.val_injective⟩ s) := by
  simp [isNIndepSet_iff, (isIndepSet_induce)]

end NIndepSet

/-! ### Graphs without independent sets -/


section IndepSetFree

variable {n : ℕ}

/-- `G.IndepSetFree n` means that `G` has no `n`-independent sets. -/
def IndepSetFree (n : ℕ) : Prop :=
  ∀ t, ¬G.IsNIndepSet n t

/-- An graph is `n`-independent set free iff its complement is `n`-clique free. -/
@[simp] theorem cliqueFree_compl : Gᶜ.CliqueFree n ↔ G.IndepSetFree n := by
  simp [IndepSetFree, CliqueFree]

/-- An graph's complement is `n`-independent set free iff it is `n`-clique free. -/
@[simp] theorem indepSetFree_compl : Gᶜ.IndepSetFree n ↔ G.CliqueFree n := by
  simp [IndepSetFree, CliqueFree]

/-- `G.IndepSetFreeOn s n` means that `G` has no `n`-independent sets contained in `s`. -/
def IndepSetFreeOn (G : SimpleGraph α) (s : Set α) (n : ℕ) : Prop :=
  ∀ ⦃t⦄, ↑t ⊆ s → ¬G.IsNIndepSet n t

end IndepSetFree

/-! ### Set of independent sets -/


section IndepSetSet

variable {n : ℕ} {s : Finset α}

/-- The `n`-independent sets in a graph as a set. -/
def indepSetSet (n : ℕ) : Set (Finset α) :=
  { s | G.IsNIndepSet n s }

variable {G}

@[simp]
theorem mem_indepSetSet_iff : s ∈ G.indepSetSet n ↔ G.IsNIndepSet n s :=
  Iff.rfl

end IndepSetSet

/-! ### Independence Number -/


section IndepNumber

variable {α : Type*} {G : SimpleGraph α}

/-- The maximal number of vertices of an independent set in a graph `G`. -/
noncomputable def indepNum (G : SimpleGraph α) : ℕ := sSup {n | ∃ s, G.IsNIndepSet n s}

@[simp] lemma cliqueNum_compl : Gᶜ.cliqueNum = G.indepNum := by
  simp [indepNum, cliqueNum]

@[simp] lemma indepNum_compl : Gᶜ.indepNum = G.cliqueNum := by
  simp [indepNum, cliqueNum]

theorem IsIndepSet.card_le_indepNum
    [Finite α] {t : Finset α} (tc : G.IsIndepSet t) : #t ≤ G.indepNum := by
  cases nonempty_fintype α
  rw [← isClique_compl] at tc
  simp_rw [indepNum, ← isNClique_compl]
  exact tc.card_le_cliqueNum

lemma exists_isNIndepSet_indepNum [Finite α] : ∃ s, G.IsNIndepSet G.indepNum s := by
  simp_rw [indepNum, ← isNClique_compl]
  exact exists_isNClique_cliqueNum

/-- An independent set in a graph `G` such that there is no independent set with more vertices. -/
@[mk_iff]
structure IsMaximumIndepSet [Fintype α] (G : SimpleGraph α) (s : Finset α) : Prop where
  isIndepSet : G.IsIndepSet s
  maximum : ∀ t : Finset α, G.IsIndepSet t → #t ≤ #s

@[simp] lemma isMaximumClique_compl [Fintype α] (s : Finset α) :
    Gᶜ.IsMaximumClique s ↔ G.IsMaximumIndepSet s := by
  simp [isMaximumIndepSet_iff, isMaximumClique_iff]

@[simp] lemma isMaximumIndepSet_compl [Fintype α] (s : Finset α) :
    Gᶜ.IsMaximumIndepSet s ↔ G.IsMaximumClique s := by
  simp [isMaximumIndepSet_iff, isMaximumClique_iff]

/-- An independent set in a graph `G` that cannot be extended by adding more vertices. -/
theorem isMaximalIndepSet_iff {s : Set α} :
    Maximal G.IsIndepSet s ↔ G.IsIndepSet s ∧ ∀ t : Set α, G.IsIndepSet t → s ⊆ t → t ⊆ s :=
  Iff.rfl

@[simp] lemma isMaximalClique_compl (s : Finset α) :
    Maximal Gᶜ.IsClique s ↔ Maximal G.IsIndepSet s := by
  simp [isMaximalIndepSet_iff, isMaximalClique_iff]

@[simp] lemma isMaximalIndepSet_compl (s : Finset α) :
    Maximal Gᶜ.IsIndepSet s ↔ Maximal G.IsClique s := by
  simp [isMaximalIndepSet_iff, isMaximalClique_iff]

lemma IsMaximumIndepSet.isMaximalIndepSet
    [Fintype α] (s : Finset α) (M : G.IsMaximumIndepSet s) : Maximal G.IsIndepSet s := by
  rw [← isMaximalClique_compl]
  rw [← isMaximumClique_compl] at M
  exact IsMaximumClique.isMaximalClique s M

theorem maximumIndepSet_card_eq_indepNum
    [Fintype α] (t : Finset α) (tmc : G.IsMaximumIndepSet t) : #t = G.indepNum := by
  rw [← isMaximumClique_compl] at tmc
  simp_rw [indepNum, ← isNClique_compl]
  exact Gᶜ.maximumClique_card_eq_cliqueNum t tmc

lemma maximumIndepSet_exists [Fintype α] : ∃ (s : Finset α), G.IsMaximumIndepSet s := by
  simp [← isMaximumClique_compl, maximumClique_exists]

end IndepNumber

/-! ### Finset of independent sets -/


section IndepSetFinset

variable [Fintype α] [DecidableEq α] [DecidableRel G.Adj] {n : ℕ} {s : Finset α}

/-- The `n`-independent sets in a graph as a finset. -/
def indepSetFinset (n : ℕ) : Finset (Finset α) := {s | G.IsNIndepSet n s}

variable {G} in
@[simp]
theorem mem_indepSetFinset_iff : s ∈ G.indepSetFinset n ↔ G.IsNIndepSet n s :=
  mem_filter.trans <| and_iff_right <| mem_univ _

end IndepSetFinset

end SimpleGraph
