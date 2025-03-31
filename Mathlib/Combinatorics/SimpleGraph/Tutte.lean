/-
Copyright (c) 2024 Pim Otte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pim Otte
-/

import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Combinatorics.SimpleGraph.UniversalVerts
import Mathlib.Data.Fintype.Card

/-!
# Tutte's theorem (work in progress)

## Main definitions
* `SimpleGraph.TutteViolator G u` is a set of vertices `u` which certifies non-existence of a
  perfect matching.
-/

namespace SimpleGraph

universe u
variable {V : Type u} {G G' : SimpleGraph V} {u x v' w : V} [Fintype V]

/-- A set certifying non-existence of a perfect matching. -/
def IsTutteViolator (G : SimpleGraph V) (u : Set V) : Prop :=
  u.ncard < ((⊤ : G.Subgraph).deleteVerts u).coe.oddComponents.ncard

/-- A graph in which the universal vertices do not violate the
Tutte-condition, if the graph decomposes into cliques, there exists a matching that covers
everything except some universal vertices.

This lemma is marked private, because
it is strictly weaker than `IsPerfectMatching.exists_of_isClique_supp` -/
private lemma Subgraph.IsMatching.exists_verts_compl_subset_universalVerts
    (h : ¬IsTutteViolator G G.universalVerts)
    (h' : ∀ (K : G.deleteUniversalVerts.coe.ConnectedComponent),
    G.deleteUniversalVerts.coe.IsClique K.supp) :
    ∃ M : Subgraph G, M.IsMatching ∧ M.vertsᶜ ⊆ G.universalVerts := by
  classical
  have hrep := ConnectedComponent.Represents.image_out
      G.deleteUniversalVerts.coe.oddComponents
  -- First we match one node from each odd component to a universal vertex
  obtain ⟨t, ht, M1, hM1⟩ := Subgraph.IsMatching.exists_of_universalVerts
      (disjoint_image_val_universalVerts _).symm (by
        simp only [IsTutteViolator, not_lt] at h
        rwa [Set.ncard_image_of_injective _ Subtype.val_injective, hrep.ncard_eq])
  -- Then we match all other nodes in components internally
  have compMatching (K : G.deleteUniversalVerts.coe.ConnectedComponent) :
      ∃ M : Subgraph G, M.verts = Subtype.val '' K.supp \ M1.verts ∧ M.IsMatching := by
    have : G.IsClique (Subtype.val '' K.supp \ M1.verts) :=
      ((h' K).of_induce).subset Set.diff_subset
    rw [← this.even_iff_exists_isMatching (Set.toFinite _), hM1.1]
    exact even_ncard_image_val_supp_sdiff_image_val_rep_union _ ht hrep
  let M2 : Subgraph G := ⨆ (K : G.deleteUniversalVerts.coe.ConnectedComponent),
    (compMatching K).choose
  have hM2 : M2.IsMatching := by
    apply Subgraph.IsMatching.iSup (fun c ↦ (compMatching c).choose_spec.2) (fun i j hij ↦ ?_)
    rw [(compMatching i).choose_spec.2.support_eq_verts,
        (compMatching j).choose_spec.2.support_eq_verts,
        (compMatching i).choose_spec.1, (compMatching j).choose_spec.1]
    exact Set.disjoint_of_subset Set.diff_subset Set.diff_subset <|
      Set.disjoint_image_of_injective Subtype.val_injective <|
        SimpleGraph.pairwise_disjoint_supp_connectedComponent _ hij
  have disjointM12 : Disjoint M1.support M2.support := by
    rw [hM1.2.support_eq_verts, hM2.support_eq_verts, Subgraph.verts_iSup,
      Set.disjoint_iUnion_right]
    exact fun K ↦ (compMatching K).choose_spec.1.symm ▸ Set.disjoint_sdiff_right
  -- The only vertices left are indeed contained in universalVerts
  have : (M1.verts ∪ M2.verts)ᶜ ⊆ G.universalVerts := by
    rw [Set.compl_subset_comm, Set.compl_eq_univ_diff]
    intro v hv
    by_cases h : v ∈ M1.verts
    · exact M1.verts.mem_union_left _ h
    right
    simp only [deleteUniversalVerts_verts, Subgraph.verts_iSup, Set.mem_iUnion, M2,
      (compMatching _).choose_spec.1]
    use (G.deleteUniversalVerts.coe.connectedComponentMk ⟨v, hv⟩)
    aesop
  exact ⟨M1 ⊔ M2, hM1.2.sup hM2 disjointM12, this⟩

/-- A graph in which the universal vertices do not violate the
Tutte-condition, if the graph decomposes into cliques, it has a perfect matching. -/
theorem Subgraph.IsPerfectMatching.exists_of_isClique_supp
    (hveven : Even (Fintype.card V)) (h : ¬G.IsTutteViolator G.universalVerts)
    (h' : ∀ (K : G.deleteUniversalVerts.coe.ConnectedComponent),
    G.deleteUniversalVerts.coe.IsClique K.supp) : ∃ (M : Subgraph G), M.IsPerfectMatching := by
  classical
  obtain ⟨M, ⟨hM, hsub⟩⟩ := IsMatching.exists_verts_compl_subset_universalVerts h h'
  obtain ⟨M', hM'⟩ := ((G.isClique_universalVerts.subset hsub).even_iff_exists_isMatching
    (Set.toFinite _)).mp (by simpa [Set.even_ncard_compl_iff hveven, -Set.toFinset_card,
      ← Set.ncard_eq_toFinset_card'] using hM.even_card)
  use M ⊔ M'
  have hspan : (M ⊔ M').IsSpanning := by
    rw [Subgraph.isSpanning_iff, Subgraph.verts_sup, hM'.1]
    exact M.verts.union_compl_self
  exact ⟨hM.sup hM'.2 (by
    simp only [hM.support_eq_verts, hM'.2.support_eq_verts, hM'.1, Subgraph.verts_sup]
    exact (Set.disjoint_compl_left_iff_subset.mpr fun ⦃a⦄ a ↦ a).symm), hspan⟩

theorem IsTutteViolator.empty (hodd : Odd (Fintype.card V)) : G.IsTutteViolator ∅ := by
  classical
  have ⟨c, hc⟩ :=
    Finite.card_pos_iff.mp
    (odd_ncard_oddComponents ((⊤ : Subgraph G).deleteVerts ∅).coe).mpr (by
    simpa [Fintype.card_congr (Equiv.Set.univ V)] using hodd).pos
  rw [IsTutteViolator, Set.ncard_empty, Set.ncard_pos]
  use c

/-- Proves the necessity part of Tutte's theorem -/
lemma not_isTutteViolator_of_isPerfectMatching {M : Subgraph G} (hM : M.IsPerfectMatching)
    (u : Set V) :
    ¬G.IsTutteViolator u := by
  simpa [IsTutteViolator, Set.Nat.card_coe_set_eq] using Finite.card_le_of_injective
      (fun c => ⟨(ConnectedComponent.odd_matches_node_outside hM c).choose,
        (ConnectedComponent.odd_matches_node_outside hM c).choose_spec.1⟩) (by
    intro x y hxy
    obtain ⟨v, hv⟩ := (ConnectedComponent.odd_matches_node_outside hM x).choose_spec.2
    obtain ⟨w, hw⟩ := (ConnectedComponent.odd_matches_node_outside hM y).choose_spec.2
    obtain ⟨v', hv'⟩ := M.isPerfectMatching_iff.mp hM _
    rw [Subtype.mk_eq_mk.mp hxy,
      (Subtype.val_injective (hv'.2 _ hw.1.symm ▸ hv'.2 _ hv.1.symm) : v = w)] at hv
    exact Subtype.mk_eq_mk.mpr <| ConnectedComponent.eq_of_common_vertex hv.2 hw.2)

end SimpleGraph
