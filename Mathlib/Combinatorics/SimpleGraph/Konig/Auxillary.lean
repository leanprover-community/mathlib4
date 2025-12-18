/-
Copyright (c) 2025 Danil Sibgatullin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Danil Sibgatullin
-/

module

public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Sym.Sym2
public import Mathlib.SetTheory.Cardinal.Arithmetic
public import Mathlib.SetTheory.Cardinal.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.Dart
public import Mathlib.Combinatorics.SimpleGraph.Matching
public import Mathlib.Combinatorics.SimpleGraph.Subgraph
public import Mathlib.Combinatorics.SimpleGraph.VertexCover

/-!
# Auxiliary lemmas for Kőnig's theorem

This file provides subgraph and cardinality lemmas used in the proofs of Kőnig’s theorem.
Main tools:

* `subgraph_upcast`: inclusion of subgraphs-of-subgraphs into the ambient graph.
* `upcast_matching`: matching is preserved under upcast.
* `card_upcast_edgeSet`: upcast preserves edge-set cardinality.
* `restricted_max_matching`: restricting a max-size matching remains max-size.
* `maximal_matching_is_cover`: maximal matchings give vertex covers.
* `konig_card_matching_le_card_cover`: `#M.edgeSet ≤ #C` for any matching `M` and vertex cover `C`.

These results are prerequisites for both the finite and general versions of Kőnig’s theorem.

## Tags
matching, vertex cover, bipartite graph, König, cardinality
-/

open Cardinal SimpleGraph SimpleGraph.Subgraph
namespace SimpleGraph

public section konig_aux

variable {V : Type*} {G : SimpleGraph V} {s t : Set V} {hbi : G.IsBipartiteWith s t}
variable {C : Set V} {M : Subgraph G} (hM : M.IsMatching)

/--
`subgraph_upcast H'` views a subgraph `H'` of the coerced graph `G'.coe` as a subgraph of the
ambient graph `G`.
-/
abbrev subgraph_upcast {G' : Subgraph G} (H' : Subgraph G'.coe) : Subgraph G :=
   H'.map ⟨Subtype.val, by intro v w h; exact G'.adj_sub h⟩

lemma upcast_matching {G' : Subgraph G} {M' : Subgraph G'.coe} :
  M'.IsMatching ↔ (subgraph_upcast M').IsMatching := by
  apply Iff.intro
  · rintro hM' v_ ⟨⟨v, hvG⟩, ⟨hvM, hvv_⟩⟩
    let ⟨w', ⟨hadj, uniq⟩⟩ := hM' hvM
    use w'
    subst hvv_
    simp only [RelHom.coeFn_mk, Subgraph.map_adj, Relation.Map, Subtype.exists, exists_and_right,
      exists_eq_right_right, Subtype.coe_eta, Subtype.coe_prop, exists_const, exists_eq_right]
    refine And.intro ⟨hvG, hadj⟩ ?_
    rintro w ⟨hvG', ⟨hwG', hadj'⟩⟩
    simp [(uniq ⟨w, hwG'⟩ hadj').symm]
  · rintro hM v' hv'M'
    let v := G'.hom v'
    have hvM : v ∈ (subgraph_upcast M').verts := ⟨v', ⟨hv'M', rfl⟩⟩
    let ⟨w, ⟨hadj, uniq⟩⟩ := hM hvM
    simp only [Subgraph.map_adj, Relation.Map, RelHom.coeFn_mk, Subtype.exists, exists_and_right,
      exists_eq_right_right, exists_eq_right, forall_exists_index] at hadj uniq
    obtain ⟨hvG', ⟨hwG', hadj'⟩⟩ := hadj
    refine ⟨⟨w, hwG'⟩, ⟨hadj', fun w' hadj' ↦ ?_⟩⟩
    have : ↑w' = w := uniq w' hvG' (G'.edge_vert <| M'.adj_sub hadj'.symm) hadj'
    simp_rw [this.symm]

lemma card_upcast_edgeSet {G' : Subgraph G} (N : Subgraph G'.coe) :
  #(subgraph_upcast N).edgeSet = #N.edgeSet := by
  simpa [subgraph_upcast] using Cardinal.mk_image_eq <| Sym2.map.injective Subtype.val_injective

@[simp]
private lemma restrict_edgeset {G' : Subgraph G} (hsub : M ≤ G')
    : #↑(Subgraph.restrict (G' := G') M).edgeSet = #M.edgeSet := by
  have edge_sub : M.edgeSet ≤ G'.edgeSet := Subgraph.edgeSet_mono hsub
  let f : (Subgraph.restrict (G' := G') M).edgeSet → M.edgeSet := fun ⟨e, he⟩ => by
    refine ⟨Sym2.map (Subtype.val) e, ?_⟩
    let ⟨⟨v, w⟩, hvw⟩ := e.exists_rep
    exact hvw ▸ (M.mem_edgeSet.mpr (hvw ▸ he).right)
  refine mk_congr <| Equiv.ofBijective f ⟨?inj, ?surj⟩ <;> simp only [f]
  · rintro ⟨_, _⟩ ⟨_, _⟩ heq
    simp only [Subtype.mk.injEq] at heq
    simpa using (Sym2.map.injective Subtype.val_injective) heq
  · rintro ⟨e, he⟩
    let ⟨⟨v, w⟩, hvw⟩ := e.exists_rep
    have adjM : M.Adj v w := M.mem_edgeSet.mp (by simpa [hvw] using he)
    have adjG' : G'.Adj v w :=  (sup_eq_right.mpr hsub) ▸ Subgraph.sup_adj.mpr <| Or.inl adjM
    exact ⟨⟨s(⟨v, G'.edge_vert adjG'⟩, ⟨w, G'.edge_vert adjG'.symm⟩), ⟨adjG', adjM⟩⟩, by simp [hvw]⟩

lemma restricted_max_matching {G' : Subgraph G} (hsub : M ≤ G') (hmax : M.IsMaxSizeMatching) :
    (Subgraph.restrict (G' := G') M).IsMaxSizeMatching := by
  let M' := Subgraph.restrict (G' := G') M
  have hM' : M'.IsMatching := hmax.left.matching_restricted hsub
  refine ⟨hM', fun L' hL' hle ↦ ?_⟩
  have := hmax.right (upcast_matching.mp hL')
  simp_all only [restrict_edgeset, card_upcast_edgeSet]

lemma maximal_matching_is_cover (hmax : M.IsMaximalMatching) : IsVertexCover G M.verts := by
  dsimp only [IsVertexCover]
  by_contra!
  obtain ⟨v, w, hadj, hnv, hnw⟩ := this
  obtain ⟨hM, hM_max⟩ := hmax
  symm_saturate
  let Mvw : Subgraph G := {
    verts := {v, w},
    Adj := fun x y ↦ (x = v ∧ y = w) ∨ (x = w ∧ y = v),
    adj_sub := by grind, edge_vert := by grind
  }
  have hMvw : Mvw.IsMatching := Subgraph.isMatching.of_connected_pair ⟨v, w, ⟨rfl, by simp [Mvw]⟩⟩
  have disj : Disjoint M.support Mvw.support := by
    intro x hxM hxMvw u hU
    simp only [hMvw.support_eq_verts, Set.le_eq_subset, Mvw, hM.support_eq_verts] at hxMvw hxM
    exact Or.elim (hxMvw hU) (fun huv => hnv <| huv ▸ (hxM hU)) (fun huw => hnw <| huw ▸ (hxM hU))
  let M' : Subgraph G :=  M ⊔ Mvw
  have hM' : M'.IsMatching := IsMatching.sup hM hMvw disj
  have hle : M ≤ M' := by simp[M']
  have : M' = M := hle.antisymm' <| hM_max hM' hle
  have heq :  M'.verts = M.verts := congrArg Subgraph.verts this
  exact absurd ((Set.ext_iff.mp heq.symm v).mpr (by simp [M', Mvw])) hnv

public lemma konig_card_matching_le_card_cover
    (hC : IsVertexCover G C) (hM : M.IsMatching) :  #M.edgeSet ≤ #C := Classical.byCases
    (p := #M.edgeSet = 0) (fun h => h ▸ Cardinal.zero_le #C) fun hnempty => by classical
  have := mk_ne_zero_iff.mp hnempty
  let e₀ : M.edgeSet := Classical.arbitrary M.edgeSet
  let f : C → M.edgeSet := fun ⟨v, hvC⟩ => if hvM : v ∈ M.verts then (hM.toEdge ⟨v, hvM⟩) else e₀
  suffices hsurj : Function.Surjective f from Cardinal.mk_le_of_surjective (f := f) hsurj
  rintro ⟨⟨v, w⟩, he⟩
  simp only [SimpleGraph.IsVertexCover] at hC
  have hadj : M.Adj v w := by simpa only [Subgraph.mem_edgeSet] using he
  have hverts : v ∈ M.verts ∧ w ∈ M.verts := ⟨M.edge_vert hadj, M.edge_vert hadj.symm⟩
  have : v ∈ C ∨ w ∈ C := hC <| M.adj_sub hadj
  rcases this with hvC | hwC <;> simp only [Subtype.exists, f]
  · refine ⟨v, ⟨hvC, ?_⟩⟩; simp [hverts, hM.toEdge_eq_of_adj hverts.left hadj]
  · refine ⟨w, ⟨hwC, ?_⟩⟩; simp [hverts, hM.toEdge_eq_of_adj hverts.right hadj.symm]

end konig_aux
end SimpleGraph
