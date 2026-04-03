/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson, Jun Kwon
-/
module

public import Mathlib.Data.Set.Lattice
public import Mathlib.Combinatorics.Graph.Subgraph

/-!
# Intersection and union of graphs

This file defines the intersection and union of graphs.

## Main definitions

- `Graph.iInter` : the intersection of a nonempty family of pairwise compatible graphs
- `Graph.sInter` : the intersection of a nonempty set of pairwise compatible graphs
- `Graph.inter` : the intersection of two graphs

-/

@[expose] public section

variable {α β ι : Type*} {x y : α} {e : β} {G G₁ G₂ H : Graph α β} {F F₀ : Set β} {X : Set α}

open Set Function

namespace Graph

section iInter

/-- The intersection of a nonempty family of pairwise compatible graphs.
Remove any disagreeing edges. -/
@[simps (attr := grind =)]
protected def iInter [Nonempty ι] (G : ι → Graph α β) : Graph α β where
  vertexSet := ⋂ i, V(G i)
  edgeSet := {e | ∃ x y, ∀ i, (G i).IsLink e x y}
  IsLink e x y := ∀ i, (G i).IsLink e x y
  isLink_symm e he x y := by simp [isLink_comm]
  eq_or_eq_of_isLink_of_isLink e _ _ _ _ h h' :=
    (h (Classical.arbitrary ι)).left_eq_or_eq (h' (Classical.arbitrary ι))
  edge_mem_iff_exists_isLink e := by simp
  left_mem_of_isLink e x y h := mem_iInter.2 fun i ↦ (h i).left_mem

protected lemma iInter_le {G : ι → Graph α β} [Nonempty ι] (i : ι) : Graph.iInter G ≤ G i where
  vertexSet_mono := iInter_subset (fun i ↦ V(G i)) i
  isLink_mono _ _ _ h := h i

@[simp]
lemma le_iInter_iff [Nonempty ι] {G : ι → Graph α β} : H ≤ Graph.iInter G ↔ ∀ i, H ≤ G i := by
  let j := Classical.arbitrary ι
  refine ⟨fun h i ↦ h.trans <| Graph.iInter_le .., fun h ↦ ?_⟩
  rw [Compatible.of_le_le (h j) (Graph.iInter_le ..) |>.le_iff]
  refine ⟨?_, fun e he ↦ ?_⟩
  · simp [fun i ↦ (h i).vertexSet_mono]
  simp only [iInter_edgeSet, mem_setOf_eq]
  obtain ⟨x, y, hbtw⟩ := exists_isLink_of_mem_edgeSet he
  use x, y, fun i ↦ (h i).isLink_mono hbtw

end iInter

section sInter

/-- The intersection of a nonempty set of pairwise compatible graphs. -/
@[simps! (attr := grind =)]
protected def sInter (s : Set (Graph α β)) (hne : s.Nonempty) : Graph α β :=
  @Graph.iInter _ _ _ hne.to_subtype (fun G : s ↦ G.1)

protected lemma sInter_le {Gs : Set (Graph α β)} (hG : G ∈ Gs) : Graph.sInter Gs ⟨G, hG⟩ ≤ G := by
  rw [Graph.sInter]
  generalize_proofs h
  exact Graph.iInter_le (⟨G, hG⟩ : Gs)

@[simp]
protected lemma le_sInter_iff {Gs : Set (Graph α β)} (hne : Gs.Nonempty) :
    H ≤ Graph.sInter Gs hne ↔ ∀ G ∈ Gs, H ≤ G := by
  simp [Graph.sInter]

end sInter

section inter

/-- The intersection of two graphs `G` and `H`. There seems to be no good way to define the junk
values so that this has the right edge and vertex set, so the edges are precisely those on which `G`
and `H` agree, and the edge set is a subset of `E(G) ∩ E(H)`, with equality if `G` and `H` are
compatible. -/
protected def inter (G H : Graph α β) : Graph α β where
  vertexSet := V(G) ∩ V(H)
  edgeSet := {e ∈ E(G) ∩ E(H) | ∀ x y, G.IsLink e x y ↔ H.IsLink e x y}
  IsLink e x y := G.IsLink e x y ∧ H.IsLink e x y
  isLink_symm _ _ _ _ h := ⟨h.1.symm, h.2.symm⟩
  eq_or_eq_of_isLink_of_isLink _ _ _ _ _ h h' := h.1.left_eq_or_eq h'.1
  edge_mem_iff_exists_isLink e := by
    simp only [edgeSet_eq_setOf_exists_isLink, mem_inter_iff, mem_setOf_eq]
    exact ⟨fun ⟨⟨⟨x, y, hexy⟩, ⟨z, w, hezw⟩⟩, h⟩ ↦ ⟨x, y, hexy, by rwa [← h]⟩,
      fun ⟨x, y, hfG, hfH⟩ ↦ ⟨⟨⟨_, _, hfG⟩, ⟨_, _, hfH⟩⟩,
      fun z w ↦ by rw [hfG.isLink_iff_sym2_eq, hfH.isLink_iff_sym2_eq]⟩⟩
  left_mem_of_isLink e x y h := ⟨h.1.left_mem, h.2.left_mem⟩

instance : Inter (Graph α β) where inter := Graph.inter

@[simp] lemma inter_vertexSet (G H : Graph α β) : V(G ∩ H) = V(G) ∩ V(H) := rfl

@[simp] lemma inter_isLink_iff : (G ∩ H).IsLink e x y ↔ G.IsLink e x y ∧ H.IsLink e x y := Iff.rfl

lemma inter_edgeSet (G H : Graph α β) :
    E(G ∩ H) = {e ∈ E(G) ∩ E(H) | ∀ x y, G.IsLink e x y ↔ H.IsLink e x y} := rfl

protected lemma inter_comm (G H : Graph α β) : G ∩ H = H ∩ G :=
  Graph.ext (Set.inter_comm ..) <| by simp [and_comm]

instance : Std.Commutative (α := Graph α β) (· ∩ ·) where
  comm G H := Graph.ext (Set.inter_comm ..) <| by simp [and_comm]

protected lemma inter_assoc (G H I : Graph α β) : (G ∩ H) ∩ I = G ∩ (H ∩ I) :=
  Graph.ext (Set.inter_assoc ..) <| by simp [and_assoc]

instance : Std.Associative (α := Graph α β) (· ∩ ·) where
  assoc _ _ _ := Graph.ext (Set.inter_assoc ..) <| by simp [and_assoc]

@[simp]
protected lemma inter_le_left : G ∩ H ≤ G where
  vertexSet_mono := inter_subset_left
  isLink_mono := by simp +contextual

@[simp] protected lemma inter_le_right : G ∩ H ≤ H := Graph.inter_comm _ _ ▸ Graph.inter_le_left

protected lemma le_inter (h₁ : H ≤ G₁) (h₂ : H ≤ G₂) : H ≤ G₁ ∩ G₂ where
  vertexSet_mono := subset_inter h₁.vertexSet_mono h₂.vertexSet_mono
  isLink_mono e x y h := by simp [h₁.isLink_mono h, h₂.isLink_mono h]

instance : SemilatticeInf (Graph α β) where
  inf := Graph.inter
  inf_le_left _ _ := Graph.inter_le_left
  inf_le_right _ _ := Graph.inter_le_right
  le_inf _ _ _ := Graph.le_inter

end inter

end Graph
