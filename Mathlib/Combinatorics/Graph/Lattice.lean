/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson, Jun Kwon
-/
module

public import Mathlib.Data.Set.Lattice
public import Mathlib.Order.ConditionallyCompletePartialOrder.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Combinatorics.Graph.Subgraph

/-!
# Intersection and union of graphs

This file defines the lattice-like structures on graphs.

## Main results

- `ConditionallyCompletePartialOrderInf (Graph α β)`
- `SemilatticeInf (Graph α β)`

## Implementation notes

Intersections are defined here as the maximal mutual subgraph of the given graphs.
This has the effect of, when taking the intersection of non-compatible graphs,
**any non-compatible edges are removed**.

-/

@[expose] public section

variable {α β ι : Type*} {x y : α} {e : β} {G G₁ G₂ H : Graph α β} {F F₀ : Set β} {X : Set α}
  {Gs : Set (Graph α β)} (Gι : ι → Graph α β) [Nonempty ι]

open Set Function WithTop

namespace Graph

noncomputable instance : ConditionallyCompletePartialOrderInf (Graph α β) where
  sInf Gs :=
    letI : DecidablePred (Set.Nonempty : Set (Graph α β) → _) := Classical.decPred _
    if hne : Gs.Nonempty then {
    vertexSet := ⋂ G ∈ Gs, V(G)
    edgeSet := {e | ∃ x y, ∀ G ∈ Gs, G.IsLink e x y}
    IsLink e x y := ∀ G ∈ Gs, G.IsLink e x y
    isLink_symm e he x y := by simp [isLink_comm]
    eq_or_eq_of_isLink_of_isLink e _ _ _ _ h h' := by
      obtain ⟨G, hG⟩ := hne
      exact (h G hG).left_eq_or_eq (h' G hG)
    left_mem_of_isLink e x y h := by
      simp only [mem_iInter]
      exact fun G hG ↦ (h G hG).left_mem} else ⊥
  isGLB_csInf_of_directed Gs hGs hGsne hGsBddB := by
    refine ⟨fun G hG ↦ ?_, fun H hH ↦ ?_⟩ <;> simp only [hGsne, ↓reduceDIte]
    · exact ⟨iInter₂_subset G hG, fun e x y => (· G hG)⟩
    refine ⟨?_, fun e x y hHxy G hG ↦ (hH hG).isLink_mono hHxy⟩
    simp only [subset_iInter_iff]
    exact fun _ hG ↦ (hH hG).vertexSet_mono

lemma isGLB_sInf_of_nonempty (hGsne : Gs.Nonempty) : IsGLB Gs (sInf Gs) := by
  refine ⟨fun G hG ↦ ?_, fun H hH ↦ ?_⟩ <;> simp only [sInf, hGsne, ↓reduceDIte]
  · exact ⟨iInter₂_subset G hG, fun e x y => (· G hG)⟩
  refine ⟨?_, fun e x y hHxy G hG ↦ (hH hG).isLink_mono hHxy⟩
  simp only [subset_iInter_iff]
  exact fun _ hG ↦ (hH hG).vertexSet_mono

@[grind =]
lemma vertexSet_sInf_eq_ite (Gs : Set (Graph α β)) [Decidable Gs.Nonempty] :
    V(sInf Gs) = if Gs.Nonempty then ⋂ G ∈ Gs, V(G) else ∅ := by
  simp only [sInf]
  split_ifs with hne <;> rfl

@[simp]
lemma vertexSet_sInf_of_nonempty (hGsne : Gs.Nonempty) : V(sInf Gs) = ⋂ G ∈ Gs, V(G) := by
  classical
  grind

@[grind =]
lemma edgeSet_sInf_eq_ite (Gs : Set (Graph α β)) [Decidable Gs.Nonempty] :
    E(sInf Gs) = if Gs.Nonempty then {e | ∃ x y, ∀ G ∈ Gs, G.IsLink e x y} else ∅ := by
  simp only [sInf]
  split_ifs with hne <;> rfl

@[simp]
lemma edgeSet_sInf_of_nonempty (hGsne : Gs.Nonempty) :
    E(sInf Gs) = {e | ∃ x y, ∀ G ∈ Gs, G.IsLink e x y} := by
  classical
  grind

@[grind =]
lemma sInf_isLink (Gs : Set (Graph α β)) [Decidable Gs.Nonempty] :
    (sInf Gs).IsLink e x y ↔ if Gs.Nonempty then ∀ G ∈ Gs, G.IsLink e x y else False := by
  simp only [sInf]
  split_ifs with hne <;> rfl

@[simp]
lemma sInf_isLink_of_nonempty (hGsne : Gs.Nonempty) :
    (sInf Gs).IsLink e x y ↔ ∀ G ∈ Gs, G.IsLink e x y := by
  classical
  grind

lemma isGLB_iInf_of_nonempty : IsGLB (range Gι) (iInf Gι) :=
  isGLB_sInf_of_nonempty <| range_nonempty_iff_nonempty.mpr ‹Nonempty ι›

@[simp]
lemma vertexSet_iInf : V(iInf Gι) = ⋂ i, V(Gι i) := by
  rw [iInf, vertexSet_sInf_of_nonempty <| range_nonempty_iff_nonempty.mpr ‹Nonempty ι›]
  exact iInf_range

@[simp]
lemma edgeSet_iInf : E(iInf Gι) = {e | ∃ x y, ∀ i, (Gι i).IsLink e x y} := by
  simp [iInf, edgeSet_sInf_of_nonempty <| range_nonempty_iff_nonempty.mpr ‹Nonempty ι›]

@[simp]
lemma iInf_isLink : (iInf Gι).IsLink e x y ↔ ∀ i, (Gι i).IsLink e x y := by
  simp [iInf, sInf_isLink_of_nonempty <| range_nonempty_iff_nonempty.mpr ‹Nonempty ι›]

/-- The infimum of two graphs `G` and `H`. The edges are precisely those on which `G` and `H` agree,
and the edge set is a subset of `E(G) ∩ E(H)`, with equality if `G` and `H` are compatible. -/
instance : SemilatticeInf (Graph α β) where
  inf G H := {
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
    left_mem_of_isLink e x y h := ⟨h.1.left_mem, h.2.left_mem⟩}
  inf_le_left G H := {
    vertexSet_mono := inter_subset_left
    isLink_mono := by simp +contextual}
  inf_le_right G H := {
    vertexSet_mono := inter_subset_right
    isLink_mono := by simp +contextual}
  le_inf H G₁ G₂ h₁ h₂ := {
    vertexSet_mono := subset_inter h₁.vertexSet_mono h₂.vertexSet_mono
    isLink_mono e x y h := by simp [h₁.isLink_mono h, h₂.isLink_mono h]}

@[simp] lemma vertexSet_inf (G H : Graph α β) : V(G ⊓ H) = V(G) ∩ V(H) := rfl

lemma edgeSet_inf (G H : Graph α β) :
    E(G ⊓ H) = {e ∈ E(G) ∩ E(H) | ∀ x y, G.IsLink e x y ↔ H.IsLink e x y} := rfl

@[simp] lemma inf_isLink : (G ⊓ H).IsLink e x y ↔ G.IsLink e x y ∧ H.IsLink e x y := Iff.rfl

@[simp]
lemma inf_inc_iff : (G ⊓ H).Inc e x ↔ ∃ y, G.IsLink e x y ∧ H.IsLink e x y := by
  simp [Inc]

@[simp]
lemma inf_isLoopAt_iff : (G ⊓ H).IsLoopAt e x ↔ G.IsLoopAt e x ∧ H.IsLoopAt e x := by
  simp [← isLink_self_iff]

@[simp]
lemma inf_isNonloopAt_iff : (G ⊓ H).IsNonloopAt e x ↔ ∃ y ≠ x, G.IsLink e x y ∧ H.IsLink e x y := by
  simp [IsNonloopAt]

@[simp] protected lemma sInf_insert (G : Graph α β) {Hs : Set (Graph α β)} (hHs : Hs.Nonempty) :
    sInf (insert G Hs) = G ⊓ sInf Hs := by
  ext <;> simp [hHs]

@[simp]
lemma inf_eq_bot_iff : G₁ ⊓ G₂ = ⊥ ↔ V(G₁) ∩ V(G₂) = ∅ := by
  rw [← vertexSet_eq_empty_iff, vertexSet_inf]

@[simp]
lemma disjoint_iff_vertexSet_disjoint : Disjoint G₁ G₂ ↔ Disjoint V(G₁) V(G₂) := by
  rw [disjoint_iff, inf_eq_bot_iff, disjoint_iff_inter_eq_empty]

lemma Compatible.edgeSet_inf (h : G.Compatible H) : E(G ⊓ H) = E(G) ∩ E(H) := by
  rw [G.edgeSet_inf]
  exact le_antisymm (fun e he ↦ he.1) fun e he ↦ ⟨he, fun _ _ ↦ h.isLink_congr he.1 he.2⟩

end Graph
