/-
Copyright (c) 2025 Danil Sibgatullin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Danil Sibgatullin
-/

module

public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.Konig.Auxillary
public import Mathlib.Combinatorics.SimpleGraph.Konig.KonigFin
public import Mathlib.Combinatorics.SimpleGraph.Matching
public import Mathlib.Combinatorics.SimpleGraph.Subgraph
public import Mathlib.Combinatorics.SimpleGraph.VertexCover
public import Mathlib.SetTheory.Cardinal.Basic
public import Mathlib.SetTheory.Cardinal.Arithmetic

/-!
# Kőnig’s theorem

This file proves Kőnig’s theorem for arbitrary bipartite simple graphs:
for a bipartite graph `G`, informingally the size of a maximum matching equals the size of a
minimum vertex cover.

The proof splits into three parts:

* the **easy direction** (`#M ≤ #C`), coming from the standard injection from
  edges of a matching into a vertex cover;
* the **hard direction, finite case** (`KonigFin.lean` and `konig_finite_graph`),
  handled by the reduction to Hall's Marriage Theorem;
* the **hard direction, infinite case** (`konig_infinite_cover`),
  handled by the construction of a maximal matching and the reduction to the finite case.

## Main statement

* `konig_bipartite` : If `G` is bipartite, `C` is a minimum vertex cover, and `M` is a
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

def IsMinSizeCover (G : SimpleGraph V) (C : Set V) : Prop :=
  IsVertexCover G C ∧ ∀ C' : Set V, IsVertexCover G C' → #C ≤ #C'

theorem min_size_cover_exists (G : SimpleGraph V) : ∃ C : Set V, IsMinSizeCover G C := by
  let S := {a : Cardinal | ∃ C : Set V, IsVertexCover G C ∧ #C = a}
  have S_nonempty : S.Nonempty := ⟨#Set.univ, ⟨Set.univ, isVertexCover_univ, rfl⟩⟩
  obtain ⟨a, ⟨C, ⟨hC, hcard⟩⟩, hmin⟩ := WellFounded.has_min Cardinal.lt_wf S S_nonempty
  refine ⟨C, ⟨hC, fun C' hC' ↦ ?_⟩⟩
  set b : S := ⟨#C', ⟨C', ⟨hC', rfl⟩⟩⟩ with hb
  have := hb ▸ hcard ▸ (hmin b b.prop)
  simpa using this

lemma konig_finite_matching
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
    edge_vert := by intros; simp only [Set.mem_union, Set.mem_range, Subtype.exists]; grind;
    symm := fun _ _ ⟨C, hC⟩ => ⟨C, Or.comm.mp hC⟩
  }
  let G' : Subgraph G := M ⊔ U
  let M' : Subgraph G'.coe := Subgraph.restrict M
  have hM' : M'.IsMaxSizeMatching := restricted_max_matching le_sup_left hM
  have hbi' := isBipartiteWith_subgraph hbi G'
  have hfinS : Finite S := Set.Finite.subset (Set.Finite.powerset hfinM) (fun A ⟨hsub, _⟩ => hsub)
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
    have hadj_coe: G'.coe.Adj ⟨v, hvG⟩ ⟨w, hwG⟩ := Or.inr ⟨⟨C, hCS⟩, Or.inl ⟨rfl, rfl⟩⟩
    rcases hC hadj_coe <;> grind
  have h : #C ≤ #M.edgeSet := by
    obtain ⟨N', ⟨hN', hN'card⟩⟩ := konig_finite_graph (G := G'.coe) (hbi := hbi') ⟨hC, hCmin⟩
    let N : Subgraph G := subgraph_upcast N'
    have hN : N.IsMatching := upcast_matching.mp hN'
    have heqN : #N.edgeSet = #N'.edgeSet := card_upcast_edgeSet N'
    have := hM.right hN; grind
  have heq_subtype : #C = #↑(Subtype.val '' C) := (Cardinal.mk_image_eq Subtype.val_injective).symm
  have covers_on_match :
    ∀ (v w : V), M.Adj v w → (∃ hvG', ⟨v, hvG'⟩ ∈ C) ∨ (∃ hwG', ⟨w, hwG'⟩ ∈ C) := by
    intro v w hadj
    have hadj' : G'.Adj v w := Or.inl hadj
    have hadj'_coe : G'.coe.Adj ⟨v, G'.edge_vert hadj'⟩ ⟨w, G'.edge_vert hadj'.symm⟩ := hadj'
    rcases hC hadj'_coe <;> grind
  have hfinC : #C < ℵ₀ := lt_of_le_of_lt h hfin
  suffices hsub: Subtype.val '' C ⊆ M.verts from ⟨hsub, heq_subtype ▸ h, by simpa⟩
  rintro v hvC
  contrapose! h
  let CinterM : Set V := ↑(Subtype.val '' C) ∩ M.verts
  have : #CinterM < #C := by
    have : CinterM ⊂ C := Set.ssubset_iff_exists.mpr (by grind)
    exact heq_subtype ▸ Cardinal.card_lt_fin_card (hfin := heq_subtype ▸ hfinC) this
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
  · use ⟨w, ⟨by simpa [hvwG] using hC, M.edge_vert hadj.symm⟩⟩
    subst hvw
    simp [f, hM.1.toEdge_eq_of_adj hvwM.2 hadj.symm]

lemma konig_infinite_cover
    (hmin : IsMinSizeCover G C) (hinf : C.Infinite)
    : ∃ M : Subgraph G, M.IsMatching ∧ #M.edgeSet = #C := by classical
  obtain ⟨M, ⟨hM, hmax⟩⟩ := exists_isMaximalMatching G
  have hle : #M.edgeSet ≤ #C := konig_card_matching_le_card_cover hmin.left hM
  refine ⟨M, ⟨hM, hle.antisymm ?_⟩⟩
  let hMverts := maximal_matching_is_cover ⟨hM, hmax⟩
  have : #↑M.verts = 2 * #↑M.edgeSet := hM.edge_card_eq_double_vert_card
  have h2ge : 2 * #↑M.edgeSet ≥ #↑C := this ▸ hmin.right M.verts hMverts
  have infM : ℵ₀ ≤ #M.edgeSet := by
    by_contra! hfinM
    have : #C ≥ ℵ₀ := Cardinal.infinite_iff.1 (Set.infinite_coe_iff.2 hinf)
    have h2inf := (two_mul #↑M.edgeSet) ▸ (le_trans this h2ge)
    exact absurd (Cardinal.add_lt_aleph0 hfinM hfinM) (not_lt_of_ge h2inf)
  have hmul2 := (two_mul #↑M.edgeSet) ▸ (Cardinal.add_eq_self infM)
  exact hmul2 ▸ h2ge

public theorem konig_bipartite
    (hbin : G.IsBipartiteWith s t) (hminC : IsMinSizeCover G C) (hmaxM : M.IsMaxSizeMatching) :
    #M.edgeSet = #C := by classical
  have hle : #↑M.edgeSet ≤ #↑C := konig_card_matching_le_card_cover hminC.left hmaxM.left
  refine hle.antisymm ?_
  by_cases hfinC : Finite C
  · have hfinM : #M.edgeSet < ℵ₀ := lt_of_le_of_lt hle (Cardinal.lt_aleph0_iff_finite.mpr hfinC)
    obtain ⟨C', hC', hcardC'⟩ := konig_finite_matching hbin hmaxM hfinM
    exact hcardC'.trans' (hminC.right C' hC')
  · obtain ⟨M', hM', hcardM'⟩ := konig_infinite_cover hminC hfinC; have := hmaxM.right hM'; grind

end Konig
end SimpleGraph
