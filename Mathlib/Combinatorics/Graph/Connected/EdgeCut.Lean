/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Mathlib.Combinatorics.Graph.Delete

/-!
# Edge cuts and bridges of graphs

This file defines the edge cuts and bridges of a graph.

## Main definitions

* `IsEdgeCut`: a set of edges between a set of vertices and its complement.
* `IsBridge`: an edge that forms a singleton edge cut (an isthmus / bridge edge).
* `IsBond`: a bond of a graph is a minimal nonempty edge cut.

-/

public section

variable {α β : Type*} {G H K : Graph α β} {S : Set α} {F F' B : Set β} {e : β} {u v : α}

open Set symmDiff

namespace Graph

/-! ### Edge cuts -/

section edgeCut

/-- The edge cut of a graph `G` along a set of vertices `S`. -/
def edgeCut (G : Graph α β) (S : Set α) : Set β := {e | ∃ u v, G.IsLink e u v ∧ u ∈ S ∧ v ∉ S}

@[inherit_doc edgeCut] scoped notation "δ(" G ", " S ")" => Graph.edgeCut G S

@[grind =]
lemma mem_edgeCut_iff (G : Graph α β) (S : Set α) :
    e ∈ δ(G, S) ↔ ∃ u v, G.IsLink e u v ∧ u ∈ S ∧ v ∉ S := Iff.rfl

lemma IsLink.mem_edgeCut_iff (h : G.IsLink e u v) :
    e ∈ δ(G, S) ↔ (u ∈ S ∧ v ∉ S) ∨ (v ∈ S ∧ u ∉ S) := by
  grind [isLink_comm, h.eq_and_eq_or_eq_and_eq]

@[grind .]
lemma edgeCut_subset (G : Graph α β) (S : Set α) : δ(G, S) ⊆ E(G) :=
  fun _ ⟨_, _, huv, _, _⟩ ↦ huv.edge_mem

lemma edgeCut_eq_empty_iff (hS : S ⊆ V(G)) : δ(G, S) = ∅ ↔ G.induce S ≤c G := by
  refine ⟨fun h ↦ IsClosedSubgraph.mk' (induce_le hS) fun e x ⟨y, hxy⟩ hxS ↦ ?_,
    fun h ↦ by grind [h.mem_iff_of_isLink]⟩
  rw [edgeSet_induce]
  use x, y, hxy, hxS
  contrapose! h
  exact ⟨e, x, y, hxy, hxS, h⟩

@[simp]
lemma edgeCut_vertexSet_diff (G : Graph α β) (S : Set α) : δ(G, V(G) \ S) = δ(G, S) := by
  grind [IsLink.left_mem, IsLink.right_mem, isLink_comm]

lemma IsSubgraph.edgeCut_eq_inter (hHG : H ≤ G) (S : Set α) : δ(H, S) = E(H) ∩ δ(G, S) := by
  grind [hHG.isLink_iff']

lemma edgeCut_symmDiff (G : Graph α β) (S S' : Set α) : δ(G, S ∆ S') = δ(G, S) ∆ δ(G, S') := by
  ext e
  wlog he : e ∈ E(G)
  · grind [IsSubgraph.isLink_iff']
  obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet he
  grind [hxy.mem_edgeCut_iff]

lemma IsClosedSubgraph.edgeCut_subset (hHG : H ≤c G) (hS : S ⊆ V(H)) : δ(G, S) ⊆ E(H) :=
  fun _ ⟨_, _, hxy, hu, _⟩ ↦ hHG.closed hxy.inc_left (hS hu)

end edgeCut

section IsEdgeCut

/-- A set of edges is an edge cut if there exists a set of vertices such that the edges in the set
are between the set of vertices and its complement. -/
def IsEdgeCut (G : Graph α β) (F : Set β) : Prop := ∃ S : Set α, δ(G, S) = F

lemma IsEdgeCut.exists (hF : G.IsEdgeCut F) : ∃ S ⊆ V(G), δ(G, S) = F := by
  obtain ⟨S, rfl⟩ := hF
  exact ⟨V(G) ∩ S, inter_subset_left .., by grind [edgeCut]⟩

lemma IsEdgeCut.exists_of_isLink (he : G.IsLink e u v) (heF : e ∈ F) (hF : G.IsEdgeCut F) :
    ∃ S ⊆ V(G), δ(G, S) = F ∧ u ∈ S ∧ v ∉ S := by
  obtain ⟨S, hS, rfl⟩ := hF.exists
  grind [he.mem_edgeCut_iff, G.edgeCut_vertexSet_diff S]

lemma IsEdgeCut.subset (hF : G.IsEdgeCut F) : F ⊆ E(G) := by
  obtain ⟨S, rfl⟩ := hF
  exact G.edgeCut_subset S

@[grind →]
lemma IsEdgeCut.symmDiff (hF : G.IsEdgeCut F) (hF' : G.IsEdgeCut F') : G.IsEdgeCut (F ∆ F') := by
  obtain ⟨S, rfl⟩ := hF
  obtain ⟨S', rfl⟩ := hF'
  use S ∆ S', G.edgeCut_symmDiff S S'

lemma IsEdgeCut.anti (hHG : H ≤ G) (hF : G.IsEdgeCut F) : H.IsEdgeCut (E(H) ∩ F) := by
  obtain ⟨S, rfl⟩ := hF
  use S
  exact hHG.edgeCut_eq_inter S

lemma IsEdgeCut.of_isClosedSubgraph (hGH : G ≤c H) (hF : G.IsEdgeCut F) : H.IsEdgeCut F := by
  obtain ⟨S, hSG, rfl⟩ := hF.exists
  use S
  ext e
  wlog he : e ∈ E(G)
  · refine iff_of_false ?_ (he <| G.edgeCut_subset _ ·)
    rintro ⟨u, v, hxy, hu, hv⟩
    exact he <| hGH.closed hxy.inc_left (hSG hu)
  obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet he
  rw [hxy.mem_edgeCut_iff, (hGH.le.isLink_mono hxy).mem_edgeCut_iff]
alias IsClosedSubgraph.isEdgeCut := IsEdgeCut.of_isClosedSubgraph

end IsEdgeCut

/-! ### Bridges: singleton edge cuts -/

section IsBridge

/-- A bridge (isthmus) is an edge that constitutes a singleton edge cut. -/
@[expose] def IsBridge (G : Graph α β) (e : β) : Prop := G.IsEdgeCut {e}

lemma IsBridge.isEdgeCut (he : G.IsBridge e) : G.IsEdgeCut {e} := he

@[grind .]
lemma IsBridge.mem_edgeSet (he : G.IsBridge e) : e ∈ E(G) := by
  simpa using IsEdgeCut.subset he

lemma IsBridge.anti_of_mem (hHG : H ≤ G) (heH : e ∈ E(H)) (he : G.IsBridge e) : H.IsBridge e := by
  obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet heH
  obtain ⟨S, hS, he⟩ := he.exists
  use S
  grind [hHG.edgeCut_eq_inter]

lemma IsBridge.of_isClosedSubgraph (hcle : H ≤c G) (he : H.IsBridge e) : G.IsBridge e := by
  obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet he.mem_edgeSet
  obtain ⟨S, hS, he⟩ := he.exists
  use S
  rwa [hcle.edgeCut_eq_inter S, inter_eq_right.mpr <| hcle.edgeCut_subset hS] at he

lemma IsClosedSubgraph.isBridge_iff (he : e ∈ E(H)) (h : H ≤c G) : G.IsBridge e ↔ H.IsBridge e :=
  ⟨fun hb ↦ hb.anti_of_mem h.le he, fun hb ↦ hb.of_isClosedSubgraph h⟩

end IsBridge

/-! ### Bonds: minimal nonempty edge cuts -/

section IsBond

/-- A bond of a graph is a minimal nonempty edge-cut. -/
@[expose]
def IsBond (G : Graph α β) (F : Set β) : Prop := Minimal (fun F ↦ G.IsEdgeCut F ∧ F.Nonempty) F

@[grind →]
lemma IsBond.subset (hB : G.IsBond B) : B ⊆ E(G) := by
  obtain ⟨h, -⟩ := hB.prop
  exact h.subset

lemma IsBond.isEdgeCut (hB : G.IsBond B) : G.IsEdgeCut B := hB.prop.1

lemma IsBond.nonempty (hB : G.IsBond B) : B.Nonempty := hB.prop.2

@[grind .]
lemma IsBridge.isBond (he : G.IsBridge e) : G.IsBond {e} := by
  refine ⟨⟨he, by simp⟩, fun F' hF' hF'e ↦ ?_⟩
  obtain rfl | rfl := subset_singleton_iff_eq.mp hF'e
  · simp at hF'
  exact hF'e

lemma IsBond.isBridge (heB : e ∈ B) (hB : G.IsBond B) : (G.deleteEdges (B \ {e})).IsBridge e := by
  have := hB.prop.1.anti (G.deleteEdges_le (F := B \ {e}))
  rw [edgeSet_deleteEdges, inter_comm, inter_diff_distrib_left, inter_eq_left.mpr hB.subset,
    inter_eq_right.mpr diff_subset] at this
  simpa [heB] using this

lemma IsBond.of_isClosedSubgraph (hGH : G ≤c H) (hB : G.IsBond B) : H.IsBond B := by
  refine ⟨⟨hB.isEdgeCut.of_isClosedSubgraph hGH, hB.nonempty⟩, fun C ⟨hC, e, heC⟩ hCB ↦ ?_⟩
  exact hB.2 ⟨hC.anti hGH.le, e, hB.subset (hCB heC), heC⟩ (inter_subset_right
  |>.trans hCB) |>.trans inter_subset_right
alias IsClosedSubgraph.isBond := IsBond.of_isClosedSubgraph

end IsBond

end Graph
