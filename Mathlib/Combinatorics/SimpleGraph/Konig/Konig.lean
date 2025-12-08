/-
Copyright (c) 2025 Danil Sibgatullin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Danil Sibgatullin
-/

import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Konig.Auxillary
import Mathlib.Combinatorics.SimpleGraph.Konig.KonigFin
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.VertexCover
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Arithmetic

/-!
# Kőnig’s theorem

This file proves Kőnig’s theorem for arbitrary bipartite simple graphs:
for a bipartite graph `G`, the size of a maximum matching equals the size of a
minimum vertex cover.

The proof splits into three parts:

* the **easy direction** (`#M ≤ #C`), coming from the standard injection from
  edges of a matching into a vertex cover;
* the **hard direction, finite case** (`KonigFin.lean` and `hard_side_finite_matching`),
  handled by the reduction to Hall's Marriage Theorem.
* the **hard direction, infinite case** (`hard_infinite_cover`),
    handled by the construction of a maximal matching and the reduction to the finite case.

## Main statement

* `konig` : If `G` is bipartite, `C` is a minimum vertex cover, and `M` is a
  maximum matching, then `#M.edgeSet = #C`.

## Tags
matching, vertex cover, bipartite, König
-/

open scoped Cardinal
open SimpleGraph

namespace SimpleGraph
namespace Konig

variable {V : Type*} {v w : V} {G : SimpleGraph V} {s t : Set V} {hbi : G.IsBipartiteWith s t}
variable {C : Set V} {M : Subgraph G} (hM : M.IsMatching)

lemma hard_side_finite_matching
    (hbi : G.IsBipartiteWith s t) (hM : M.IsMaxSizeMatching) (hfin : #M.edgeSet < ℵ₀)
    : ∃ C : Set V, G.IsVertexCover C ∧ #C ≤ #M.edgeSet := by classical
  by_contra! hnc
  let S := {A : Set V | A ⊆ M.verts ∧ #A ≤ #M.edgeSet ∧ ∀ v w, M.Adj v w → (v ∈ A) ∨ (w ∈ A)}
  have witnesses : ∀ A ∈ S, ∃ x y, G.Adj x y ∧ x ∉ A ∧ y ∉ A := by
    rintro r ⟨_, h, _⟩
    contrapose! h
    suffices hr : G.IsVertexCover r from by simpa using not_le.mpr (hnc r hr)
    intro v w hadj
    exact or_iff_not_imp_left.mpr (h v w hadj)
  choose fx_ fy_ hf using witnesses
  let fx : S → V := fun r => fx_ r.1 r.2; let fy : S → V := fun r => fy_ r.1 r.2
  have : #↑M.verts = 2 * #↑M.edgeSet := hM.left.edge_card_eq_double_vert_card
  have hfinM : M.verts.Finite := Cardinal.lt_aleph0_iff_finite.mp <|
    this ▸ (Cardinal.mul_lt_aleph0_iff.mpr (Or.inr (Or.inr ⟨Cardinal.nat_lt_aleph0 2, hfin⟩)))
  let U : Subgraph G := {
    verts := (Set.range fx) ∪ (Set.range fy),
    Adj := fun v w => ∃ r : S, (fx r = v ∧ fy r = w) ∨ (fx r = w ∧ fy r = v)
    adj_sub := fun ⟨r, hr⟩ => by
      have := (hf r.val r.prop).left
      symm_saturate
      rcases hr with ⟨hrx, hry⟩ | ⟨hrx, hry⟩ <;> simpa [←hrx, ←hry]

    edge_vert := fun ⟨r, hr⟩ => by
      simp only [Set.mem_union, Set.mem_range, Subtype.exists]
      rcases hr with ⟨h, _⟩ | ⟨_, h⟩
      · left; exact ⟨r.1, ⟨r.2, h⟩⟩
      · right; exact ⟨r.1, ⟨r.2, h⟩⟩

    symm := fun _ _ ⟨C, hC⟩ => ⟨C, Or.comm.mp hC⟩
  }
  let G' : Subgraph G := M ⊔ U
  let M' : Subgraph G'.coe := Subgraph.restrict M
  have hM' : M'.IsMaxSizeMatching := restricted_max_matching le_sup_left hM
  have hbi' := isBipartiteWith_subgraph hbi G'
  have hfinS : Finite S := by
    refine Set.Finite.subset (Set.Finite.powerset hfinM) ?_ -- through 𝒫 M.verts
    rintro A ⟨hsub, _⟩; exact hsub
  have : G'.verts.Finite := by
    refine Set.Finite.union hfinM <| Set.Finite.union ?_ ?_ <;> apply Set.finite_range
  have hfinG' : Fintype G'.verts := this.fintype
  let ⟨C, ⟨hC, hCmin⟩⟩ := min_size_cover_exists (G := G'.coe)
  suffices hCS : ↑C ∈ S from by
    let CS : S := ⟨C, hCS⟩
    let v := fx CS
    let w := fy CS
    have hvG: v ∈ G'.verts := Or.inr (Or.inl ⟨CS, rfl⟩)
    have hwG: w ∈ G'.verts := Or.inr (Or.inr ⟨CS, rfl⟩)
    obtain ⟨hadj, hnv, hnw⟩ := hf C hCS;
    simp at hnv hnw
    have hadj_coe: G'.coe.Adj ⟨v, hvG⟩ ⟨w, hwG⟩ := Or.inr ⟨⟨C, hCS⟩, Or.inl ⟨rfl, rfl⟩⟩
    rcases hC hadj_coe with hv | hw
    · exact absurd hv <| hnv hvG
    · exact absurd hw <| hnw hwG
  have h : #C ≤ #M.edgeSet := by
    obtain ⟨N', ⟨hN', hN'card⟩⟩ := hard_side_finite_graph (G := G'.coe) (hbi := hbi') ⟨hC, hCmin⟩
    let N : Subgraph G := subgraph_upcast N'
    have hN : N.IsMatching := upcast_matching.mp hN'
    have heqN : #N.edgeSet = #N'.edgeSet := card_upcast_edgeSet N'
    exact hN'card ▸ heqN ▸ (hM.right N hN)
  have heq_subtype : #C = #↑(Subtype.val '' C) := (Cardinal.mk_image_eq Subtype.val_injective).symm
  have covers_on_match :
    ∀ (v w : V), M.Adj v w → (∃ hvG', ⟨v, hvG'⟩ ∈ C) ∨ (∃ hwG', ⟨w, hwG'⟩ ∈ C) := by
    intro v w hadj
    have hadj' : G'.Adj v w := Or.inl hadj
    have hadj'_coe : G'.coe.Adj ⟨v, G'.edge_vert hadj'⟩ ⟨w, G'.edge_vert hadj'.symm⟩ := hadj'
    rcases hC hadj'_coe with hv | hw
    · exact Or.inl ⟨G'.edge_vert hadj', hv⟩
    · exact Or.inr ⟨G'.edge_vert hadj'.symm, hw⟩
  have hfinC : #C < ℵ₀ := lt_of_le_of_lt h hfin
  suffices hsub: Subtype.val '' C ⊆ M.verts
      from ⟨hsub, heq_subtype ▸ h, (by simp; exact covers_on_match)⟩
  rintro v hvC
  contrapose! h
  let CinterM : Set V := ↑(Subtype.val '' C) ∩ M.verts
  have : #CinterM < #C := by
    have : CinterM < C :=
      Set.ssubset_iff_exists.mpr ⟨by simp[CinterM], ⟨v, by simp[CinterM, h, hvC]⟩⟩
    exact heq_subtype ▸ Cardinal.card_ssubset' (hfin := heq_subtype ▸ hfinC) this
  suffices hcard : #M.edgeSet ≤ #CinterM from lt_of_le_of_lt hcard this
  let f : CinterM → M.edgeSet := fun ⟨w, ⟨hwC, hwM⟩⟩ => hM.1.toEdge ⟨w, hwM⟩
  refine Cardinal.mk_le_of_surjective (f := f) (fun ⟨e, he⟩ => ?_)
  let ⟨⟨v, w⟩, hvw⟩ := e.exists_rep
  have hadj := Subgraph.mem_edgeSet.mp (hvw ▸ he)
  have hvwM : v ∈ M.verts ∧ w ∈ M.verts := ⟨M.edge_vert hadj, M.edge_vert hadj.symm⟩
  have hvwG : v ∈ G'.verts ∧ w ∈ G'.verts := ⟨Or.inl hvwM.1, Or.inl hvwM.2⟩
  have : G'.coe.Adj ⟨v, hvwG.1⟩ ⟨w, hvwG.2⟩ := Or.inl hadj
  rcases hC this with hC | hC
  · use ⟨v, ⟨by simpa [hvwG] using hC, M.edge_vert hadj⟩⟩
    simpa [f, hvw] using hM.1.toEdge_eq_of_adj hvwM.1 hadj
  · use ⟨w, ⟨by simpa [hvwG] using hC, M.edge_vert hadj.symm⟩⟩; subst hvw
    simp [f, hM.1.toEdge_eq_of_adj hvwM.2 hadj.symm]

lemma hard_infinite_cover
    (hmin : G.IsMinSizeCover C) (hinf : C.Infinite)
    : ∃ M : Subgraph G, M.IsMatching ∧ #M.edgeSet = #C := by classical
  obtain ⟨M, ⟨hM, hmax⟩⟩ := exists_maximal_matching (G := G)
  have hle : #M.edgeSet ≤ #C := konig_easy_side hmin.left hM
  refine ⟨M, And.intro hM ?_⟩
  let hMverts := maximal_matching_is_cover ⟨hM, hmax⟩
  have : #↑M.verts = 2 * #↑M.edgeSet := hM.edge_card_eq_double_vert_card
  have h2ge : 2 * #↑M.edgeSet ≥ #↑C := this ▸ hmin.right M.verts hMverts
  have infM : ℵ₀ ≤ #M.edgeSet := by
    by_contra! hfinM
    have : #C ≥ ℵ₀ := Cardinal.infinite_iff.1 (Set.infinite_coe_iff.2 hinf)
    have h2inf := (two_mul #↑M.edgeSet) ▸ (le_trans this h2ge)
    exact absurd (Cardinal.add_lt_aleph0 hfinM hfinM) (not_lt_of_ge h2inf)
  have hmul2 := (two_mul #↑M.edgeSet) ▸ (Cardinal.add_eq_self infM)
  exact le_antisymm hle <| hmul2 ▸ h2ge

theorem konig
    (hbin : G.IsBipartiteWith s t) (hminC : G.IsMinSizeCover C) (hmaxM : M.IsMaxSizeMatching) :
    #M.edgeSet = #C := by classical
  have hle : #↑M.edgeSet ≤ #↑C := konig_easy_side hminC.left hmaxM.left
  refine le_antisymm hle ?_
  by_cases hfinC : Finite C
  · have hfinM : #M.edgeSet < ℵ₀ := lt_of_le_of_lt hle (Cardinal.lt_aleph0_iff_finite.mpr hfinC)
    obtain ⟨C', hC', hcardC'⟩ := (hard_side_finite_matching hbin hmaxM hfinM)
    exact le_trans (hminC.right C' hC') hcardC'
  · obtain ⟨M', hM', hcardM'⟩ := hard_infinite_cover hminC hfinC
    exact hcardM' ▸ (hmaxM.right M' hM')

end Konig
end SimpleGraph
