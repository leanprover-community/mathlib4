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
# Partial proof of Tutte's theorem
-/
namespace SimpleGraph

universe u
variable {V : Type u} {G G' : SimpleGraph V} {u x v' w : V}

/--
-/
def TutteViolator (G: SimpleGraph V) (u : Set V) : Prop :=
  u.ncard < {c : ((⊤ : G.Subgraph).deleteVerts u).coe.ConnectedComponent | Odd (c.supp.ncard)}.ncard

lemma quot_out_inj (r : V → V → Prop): Function.Injective (@Quot.out _ r) :=
  fun v w h ↦ by simpa [Quot.out_eq] using (congrArg _ h : Quot.mk r v.out = Quot.mk r w.out)

--Temporarily inlined from #20705, will be removed before merge
theorem IsClique.of_induce {S : Subgraph G} {F : Set V} {A : Set F}
    (c : (S.induce F).coe.IsClique A) : G.IsClique (Subtype.val '' A) := by
  simp only [Set.Pairwise, Set.mem_image, Subtype.exists, exists_and_right, exists_eq_right]
  intro _ ⟨_, ainA⟩ _ ⟨_, binA⟩ anb
  exact S.adj_sub (c ainA binA (Subtype.coe_ne_coe.mp anb)).2.2

theorem IsMatching.exists_verts_compl_subset_universalVerts [Fintype V]
    (h : ¬TutteViolator G G.universalVerts)
    (h' : ∀ (K : G.deleteUniversalVerts.coe.ConnectedComponent),
    G.deleteUniversalVerts.coe.IsClique K.supp) :
    ∃ (M : Subgraph G), M.IsMatching ∧ M.vertsᶜ ⊆ G.universalVerts := by
  classical
  obtain ⟨t, ht, M1, hM1⟩ := Subgraph.IsMatching.exists_of_universalVerts
      (disjoint_image_val_universalVerts _).symm (by
        simp only [TutteViolator, not_lt] at h
        rwa [Set.ncard_image_of_injective _ Subtype.val_injective,
        Set.ncard_image_of_injective _ (quot_out_inj _)])

  have compMatching (K : G.deleteUniversalVerts.coe.ConnectedComponent) :
      ∃ M : Subgraph G, M.verts = Subtype.val '' K.supp \ M1.verts ∧ M.IsMatching := by
    have : G.IsClique (Subtype.val '' K.supp \ M1.verts) :=
      ((h' K).of_induce).subset Set.diff_subset
    rw [← this.even_iff_matches (Set.toFinite _), hM1.1]
    exact even_ncard_supp_sdiff_rep_union _ ht (ConnectedComponent.Represents.image_out
      G.deleteUniversalVerts.coe.oddComponents)
  let M2 : Subgraph G := (⨆ (K : G.deleteUniversalVerts.coe.ConnectedComponent),
    (compMatching K).choose)

  have hM2 : M2.IsMatching := by
    apply Subgraph.IsMatching.iSup (fun c => (compMatching c).choose_spec.2)
    intro i j hij
    rw [(compMatching i).choose_spec.2.support_eq_verts,
        (compMatching j).choose_spec.2.support_eq_verts,
        (compMatching i).choose_spec.1, (compMatching j).choose_spec.1]
    exact Set.disjoint_of_subset (Set.diff_subset) (Set.diff_subset) <|
      Set.disjoint_image_of_injective Subtype.val_injective
        (SimpleGraph.pairwise_disjoint_supp_connectedComponent _ hij)

  have disjointM12 : Disjoint M1.verts M2.verts := by
    rw [Subgraph.verts_iSup, Set.disjoint_iUnion_right]
    exact fun K ↦ (compMatching K).choose_spec.1.symm ▸ Set.disjoint_sdiff_right

  have sub : (M1.verts ∪ M2.verts)ᶜ ⊆ G.universalVerts := by
    rw [Set.compl_subset_comm, Set.compl_eq_univ_diff]
    intro v hv
    by_cases h : v ∈ M1.verts
    · exact M1.verts.mem_union_left _ h
    right
    simp only [deleteUniversalVerts_verts, Subgraph.verts_iSup, Set.mem_iUnion, M2,
      (compMatching _).choose_spec.1]
    use (G.deleteUniversalVerts.coe.connectedComponentMk ⟨v, hv⟩)
    aesop

  exact ⟨M1 ⊔ M2, hM1.2.sup hM2 (hM1.2.support_eq_verts ▸ hM2.support_eq_verts ▸ disjointM12), sub⟩

theorem tutte_part' [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
  (hveven : Even (Fintype.card V))
  (h : ¬G.TutteViolator G.universalVerts)
  (h' : ∀ (K : G.deleteUniversalVerts.coe.ConnectedComponent), G.deleteUniversalVerts.coe.IsClique K.supp) :
    ∃ (M : Subgraph G), M.IsPerfectMatching := by
  classical
  obtain ⟨M, ⟨hM, sub⟩⟩ := IsMatching.exists_verts_compl_subset_universalVerts h h'

  have subM1M2Clique : G.IsClique M.vertsᶜ := by
    exact G.isClique_universalVerts.subset sub

  have evensubM1M2 : Even (M.vertsᶜ).ncard := by
    rw [Set.compl_eq_univ_diff, Set.ncard_diff (by intro v _; trivial), Nat.even_sub (Set.ncard_le_ncard (by intro v _; trivial))]
    rw [Fintype.card_eq_nat_card, ← Set.ncard_univ] at hveven
    simp [hveven, show Even M.verts.ncard from by
      simpa [-Set.toFinset_card,← Set.toFinset_union, ← Set.ncard_eq_toFinset_card'] using hM.even_card]
  obtain ⟨M3, hM3⟩ := (subM1M2Clique.even_iff_matches (Set.toFinite _)).mp evensubM1M2

  let Mcon := M ⊔ M3
  use Mcon

  have MconSpan : Mcon.IsSpanning := by
    rw [Subgraph.isSpanning_iff, Subgraph.verts_sup, hM3.1]
    exact Set.union_compl_self M.verts
  refine ⟨?_, MconSpan⟩
  unfold Mcon
  exact hM.sup hM3.2 (by
    simp only [hM.support_eq_verts, hM3.2.support_eq_verts, hM3.1, Subgraph.verts_sup]
    exact (Set.disjoint_compl_left_iff_subset.mpr fun ⦃a⦄ a ↦ a).symm
    )
theorem empty_tutteViolator [Fintype V] (hodd : Odd (Fintype.card V)) : G.TutteViolator ∅ := by
  classical
  have ⟨c, hc⟩ := Classical.inhabited_of_nonempty
    (Finite.card_pos_iff.mp <| Odd.pos <|
    (odd_card_iff_odd_components ((⊤ : Subgraph G).deleteVerts ∅).coe).mp (by
    simpa [Fintype.card_congr (Equiv.Set.univ V)] using hodd))
  rw [TutteViolator, Set.ncard_empty, Set.ncard_pos]
  use c

lemma tutte_necessary [Fintype V]
  {M : Subgraph G} (hM : M.IsPerfectMatching) (u : Set V) : ¬G.TutteViolator u := by
  simpa [TutteViolator, Set.Nat.card_coe_set_eq] using Finite.card_le_of_injective
      (fun c => ⟨(c.1.odd_matches_node_outside hM c.2).choose,
        (c.1.odd_matches_node_outside hM c.2).choose_spec.1⟩) (by
    intro x y hxy
    obtain ⟨v, hv⟩:= (x.1.odd_matches_node_outside hM x.2).choose_spec.2
    obtain ⟨w, hw⟩:= (y.1.odd_matches_node_outside hM y.2).choose_spec.2
    obtain ⟨v', hv'⟩ := (M.isPerfectMatching_iff).mp hM _
    rw [Subtype.mk_eq_mk.mp hxy,
      (Subtype.val_injective (hv'.2 _ hw.1.symm ▸ hv'.2 _ hv.1.symm) : v = w)] at hv
    exact Subtype.mk_eq_mk.mpr <| ConnectedComponent.eq_of_common_vertex hv.2 hw.2)

end SimpleGraph
