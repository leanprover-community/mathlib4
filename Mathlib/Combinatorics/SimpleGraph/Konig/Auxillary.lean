/-
Copyright (c) 2025 Danil Sibgatullin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Danil Sibgatullin
-/

import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Sym.Sym2
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Dart
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.VertexCover
open Cardinal SimpleGraph SimpleGraph.Subgraph

/-!
# Auxiliary lemmas for Kőnig's theorem

This file provides subgraph and cardinality lemmas used in the proofs of Kőnig’s theorem.
Main tools:

* `subgraph_upcast`: inclusion of subgraphs-of-subgraphs into the ambient graph.
* `upcast_matching`: matching is preserved under upcast.
* `card_upcast_edgeSet`: upcast preserves edge-set cardinality.
* `restricted_max_matching`: restricting a max-size matching remains max-size.
* `maximal_matching_is_cover`: maximal matchings give vertex covers.
* `konig_easy_side`: `#M.edgeSet ≤ #C` for any matching `M` and vertex cover `C`.

These results are prerequisites for both the finite and general versions of Kőnig’s theorem.

## Tags
matching, vertex cover, bipartite graph, König, cardinality
-/

variable {V : Type*} {G : SimpleGraph V} {s t : Set V} {hbi : G.IsBipartiteWith s t}
variable {C : Set V} {M : Subgraph G} (hM : M.IsMatching)

namespace SimpleGraph
namespace Konig

abbrev subgraph_upcast {G' : Subgraph G} (H' : Subgraph G'.coe) : Subgraph G :=
   H'.map ⟨Subtype.val, by intro v w h; exact G'.adj_sub h⟩

lemma upcast_matching {G' : Subgraph G} {M' : Subgraph G'.coe} :
  M'.IsMatching ↔ (subgraph_upcast M').IsMatching := by
  apply Iff.intro
  · rintro hM' v_ ⟨⟨v, hvG⟩, ⟨hvM, hvv_⟩⟩
    let ⟨w', ⟨hadj, uniq⟩⟩ := hM' hvM
    use w'; subst hvv_
    simp [Subtype.forall, Relation.Map] at hadj uniq ⊢
    refine And.intro ⟨hvG, hadj⟩ ?_
    intro w _ hwG hadj'
    simp_rw [(uniq w hwG hadj').symm]
  · rintro hM v' hv'M'
    let v := G'.hom v'
    have hvM : v ∈ (subgraph_upcast M').verts := ⟨v', ⟨hv'M', rfl⟩⟩
    let ⟨w, ⟨hadj, uniq⟩⟩ := hM hvM
    simp [Relation.Map] at hadj uniq
    obtain ⟨hvG', ⟨hwG', hadj'⟩⟩ := hadj
    use ⟨w, hwG'⟩
    refine And.intro hadj' ?_
    intro w' hadj'
    have : ↑w' = w := uniq w' hvG' (G'.edge_vert <| M'.adj_sub hadj'.symm) hadj'
    simp_rw [this.symm]

lemma card_upcast_edgeSet {G' : Subgraph G} (N : Subgraph G'.coe) :
  #(subgraph_upcast N).edgeSet = #N.edgeSet := by
  simpa [subgraph_upcast] using Cardinal.mk_image_eq <| Sym2.map.injective Subtype.val_injective

private lemma restrict_edgeset {G' : Subgraph G} (hsub : M ≤ G')
    : #↑(Subgraph.restrict (G' := G') M).edgeSet = #M.edgeSet := by
  have edge_sub : M.edgeSet ≤ G'.edgeSet := Subgraph.edgeSet_mono hsub
  let f : (Subgraph.restrict (G' := G') M).edgeSet → M.edgeSet := fun ⟨e, he⟩ => by
    refine ⟨Sym2.map (Subtype.val) e, ?_⟩
    let ⟨⟨v, w⟩, hvw⟩ := e.exists_rep
    exact hvw ▸ (M.mem_edgeSet.mpr (hvw ▸ he).right)
  refine mk_congr <| Equiv.ofBijective f ⟨?inj, ?surj⟩ <;> simp [f]
  · rintro ⟨_, _⟩ ⟨_, _⟩ heq
    simp at heq
    simpa using (Sym2.map.injective Subtype.val_injective) heq
  · rintro ⟨e, he⟩
    let ⟨⟨v, w⟩, hvw⟩ := e.exists_rep
    have adjM : M.Adj v w := M.mem_edgeSet.mp (by simpa [hvw] using he)
    have adjG' : G'.Adj v w :=
      (sup_eq_right.mpr hsub) ▸ Subgraph.sup_adj.mpr <| Or.inl adjM
    exact ⟨⟨s(⟨v, G'.edge_vert adjG'⟩, ⟨w, G'.edge_vert adjG'.symm⟩), ⟨adjG', adjM⟩⟩, by simp [hvw]⟩

lemma restricted_max_matching {G' : Subgraph G} (hsub : M ≤ G') (hM : M.IsMaxSizeMatching) :
    (Subgraph.restrict (G' := G') M).IsMaxSizeMatching := by
  let M' := Subgraph.restrict (G' := G') M
  have hM' : M'.IsMatching := hM.left.matching_restricted hsub
  refine And.intro hM' ?_
  intro L' hL'
  let L : Subgraph G := subgraph_upcast L'
  have LleM : #L.edgeSet ≤ #M.edgeSet := hM.right L (upcast_matching.mp hL')
  exact (restrict_edgeset hsub) ▸ (card_upcast_edgeSet L') ▸ LleM

lemma maximal_matching_is_cover (hmax : M.IsMaximalMatching) : G.IsVertexCover M.verts := by
  dsimp only [SimpleGraph.IsVertexCover]
  by_contra!
  obtain ⟨v, w, hadj, hnv, hnw⟩ := this
  obtain ⟨hM, hM_max⟩ := hmax
  symm_saturate
  let Mvw : Subgraph G := {
    verts := {v, w},
    Adj := fun x y => (x = v ∧ y = w) ∨ (x = w ∧ y = v),
    adj_sub := fun h => by (rcases h with h | h <;> simpa [h.1, h.2])
    edge_vert := fun h => by (rcases h with h | h <;> simp [h, or_true])
  }
  have hMvw : Mvw.IsMatching := Subgraph.isMatching.of_connected_pair ⟨v, w, ⟨rfl, by simp [Mvw]⟩⟩
  have disj : Disjoint M.support Mvw.support := by
    by_contra! hcontra
    simp_all only
      [Disjoint, not_forall, IsMatching.support_eq_verts hM, IsMatching.support_eq_verts hMvw]
    obtain ⟨S, hSleqM, hSlevw, hSnbot⟩ := hcontra
    suffices hSub : S ⊆ (∅ : Set V) from hSnbot hSub
    intro x hx
    rcases hSlevw hx with rfl | rfl
    · exact hnv (hSleqM hx)
    · exact hnw (hSleqM hx)
  let M' : Subgraph G :=  M ⊔ Mvw
  have hM' : M'.IsMatching := IsMatching.sup hM hMvw disj
  have hle : M ≤ M' := by simp[M']
  have : M' = M := hM_max M' hM' hle
  have heq :  M'.verts = M.verts := congrArg Subgraph.verts this
  exact absurd ((Set.ext_iff.mp heq.symm v).mpr (by simp [M', Mvw])) hnv

lemma konig_easy_side
    (hC : G.IsVertexCover C) (hM : M.IsMatching) :  #M.edgeSet ≤ #C := Classical.byCases
    (p := #M.edgeSet = 0) (fun h => h ▸ Cardinal.zero_le #C) fun hnempty => by classical
  have := mk_ne_zero_iff.mp hnempty
  let e₀ : M.edgeSet := Classical.arbitrary M.edgeSet
  let f : C → M.edgeSet := fun ⟨v, hvC⟩ =>
    if hvM : v ∈ M.verts then (hM.toEdge ⟨v, hvM⟩) else e₀
  suffices hsurj : Function.Surjective f from  Cardinal.mk_le_of_surjective (f := f) hsurj
  rintro ⟨⟨v, w⟩, he⟩
  simp only [SimpleGraph.IsVertexCover] at hC
  have hadj : M.Adj v w := by simpa only [Subgraph.mem_edgeSet] using he
  have hverts : v ∈ M.verts ∧ w ∈ M.verts := ⟨M.edge_vert hadj, M.edge_vert hadj.symm⟩
  have := hC <| M.adj_sub hadj
  rcases this with hvC | hwC <;> simp [f]
  · refine ⟨v, ⟨hvC, ?_⟩⟩; simp [hverts, hM.toEdge_eq_of_adj hverts.left hadj]
  · refine ⟨w, ⟨hwC, ?_⟩⟩; simp [hverts, hM.toEdge_eq_of_adj hverts.right hadj.symm]

end Konig
end SimpleGraph
