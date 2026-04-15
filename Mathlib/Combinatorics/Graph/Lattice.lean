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

- `CompleteSemilatticeInf (WithTop (Graph α β))`
- `ConditionallyCompletePartialOrderInf (Graph α β)`
- `SemilatticeInf (Graph α β)`

## Implementation notes

Intersections are defined here as the maximal mutual subgraph of the given graphs.
This has the effect of, when taking the intersection of non-compatible graphs,
**any non-compatible edges are removed**.

-/

@[expose] public section

variable {α β ι : Type*} {x y : α} {e : β} {G G₁ G₂ H : Graph α β} {F F₀ : Set β} {X : Set α}

open Set Function WithTop

namespace Graph

def ExtendedGraph (α β : Type*) := WithTop (Graph α β)
deriving PartialOrder, OrderTop, OrderBot

noncomputable instance : CompleteSemilatticeInf (ExtendedGraph α β) where
  sInf Gs :=
    letI : DecidablePred (Set.Nonempty : Set (Graph α β) → _) := Classical.decPred _
    if hne : (WithTop.some ⁻¹' Gs).Nonempty then WithTop.some ({
    vertexSet := ⋂ G ∈ WithTop.some ⁻¹' Gs, V(G)
    edgeSet := {e | ∃ x y, ∀ G ∈ WithTop.some ⁻¹' Gs, G.IsLink e x y}
    IsLink e x y := ∀ G ∈ WithTop.some ⁻¹' Gs, G.IsLink e x y
    isLink_symm e he x y := by simp [isLink_comm]
    eq_or_eq_of_isLink_of_isLink e _ _ _ _ h h' := by
      obtain ⟨G, hG⟩ := hne
      exact (h G hG).left_eq_or_eq (h' G hG)
    left_mem_of_isLink e x y h := by
      simp only [mem_preimage, mem_iInter]
      exact fun G hG ↦ (h G hG).left_mem} : Graph α β) else ⊤
  isGLB_sInf Gs := by
    refine ⟨fun G hG => ?_, fun H hH => ?_⟩
    · obtain rfl | htop := eq_or_ne G ⊤
      · exact le_top
      unfold ExtendedGraph at G Gs ⊢
      lift G to Graph α β using htop
      have hGs : (WithTop.some ⁻¹' Gs).Nonempty := ⟨G, by simpa⟩
      simp only [hGs, ↓reduceDIte, ge_iff_le]
      refine coe_le_coe.mpr ⟨fun _ ↦ ?_, fun _ _ _ ↦ ?_⟩
        <;> simp only [mem_preimage, mem_iInter] <;> exact (· G hG)
    unfold ExtendedGraph at H Gs
    obtain rfl | htop := eq_or_ne H ⊤
    · suffices ¬ (WithTop.some ⁻¹' Gs).Nonempty by simp [this]
      simp only [not_nonempty_iff_eq_empty, preimage_eq_empty_iff, disjoint_right, mem_range,
        forall_exists_index, forall_apply_eq_imp_iff]
      exact fun _ hHs => Option.some_ne_none _ (top_le_iff.mp <| hH hHs)
    lift H to Graph α β using htop
    split_ifs with hne
    · exact coe_le_coe.mpr {
        vertexSet_mono := by
          simp only [subset_iInter_iff]
          exact fun G hG ↦ (coe_le_coe.mp <| hH hG).vertexSet_mono
        isLink_mono e x y hHxy G hG := (coe_le_coe.mp <| hH hG).isLink_mono hHxy}
    exact le_top

lemma sInf_eq_top_iff (Gs : Set (ExtendedGraph α β)) : sInf Gs = ⊤ ↔ Gs ⊆ {⊤} := by
  classical
  refine ⟨fun h G hG => top_le_iff.mp (h ▸ show sInf Gs ≤ G from sInf_le hG), fun h => ?_⟩
  obtain rfl | rfl := subset_singleton_iff_eq.mp h
  · exact isGLB_empty.sInf_eq
  exact sInf_singleton

noncomputable instance : ConditionallyCompletePartialOrderInf (Graph α β) where
  sInf Gs :=
    letI : DecidablePred (Set.Nonempty : Set (Graph α β) → _) := Classical.decPred _
    (sInf (WithTop.some '' Gs) : ExtendedGraph α β).untopD ⊥
  isGLB_csInf_of_directed Gs hGs hGsne hGsBddB := by
    classical
    refine ⟨fun G hG => (untopD_le <| sInf_le (α := ExtendedGraph α β) (by use G)), fun H hH ↦ ?_⟩
    change H ≤ (untopD ⊥ (if hne : Set.Nonempty _ then _ else _))
    simp only [ExtendedGraph, coe_injective.preimage_image, hGsne, ↓reduceDIte, untopD_coe]
    exact { vertexSet_mono := by
              simp only [subset_iInter_iff]
              exact fun _ hG ↦ (hH hG).vertexSet_mono
            isLink_mono e x y hHxy G hG := (hH hG).isLink_mono hHxy}

lemma isGLB_sInf_of_nonempty {Gs : Set (Graph α β)} (hGsne : Gs.Nonempty) : IsGLB Gs (sInf Gs) := by
  classical
  refine ⟨fun G hG ↦ (untopD_le <| sInf_le (α := ExtendedGraph α β) (by use G)), fun H hH ↦ ?_⟩
  change H ≤ (untopD ⊥ (if hne : Set.Nonempty _ then _ else _))
  simp only [ExtendedGraph, coe_injective, preimage_image_eq, hGsne, ↓reduceDIte, untopD_coe]
  exact { vertexSet_mono := by
            simp only [subset_iInter_iff]
            exact fun _ hG ↦ (hH hG).vertexSet_mono
          isLink_mono e x y hHxy G hG := (hH hG).isLink_mono hHxy}

@[grind =]
lemma vertexSet_sInf_eq_ite (Gs : Set (Graph α β)) [Decidable Gs.Nonempty] :
    V(sInf Gs) = if Gs.Nonempty then ⋂ G ∈ Gs, V(G) else ∅ := by
  simp only [sInf, ExtendedGraph, coe_injective.preimage_image]
  split_ifs with hne <;> rfl

@[simp]
lemma vertexSet_sInf_of_nonempty {Gs : Set (Graph α β)} (hGsne : Gs.Nonempty) :
    V(sInf Gs) = ⋂ G ∈ Gs, V(G) := by
  classical
  grind

@[grind =]
lemma edgeSet_sInf_eq_ite (Gs : Set (Graph α β)) [Decidable Gs.Nonempty] :
    E(sInf Gs) = if Gs.Nonempty then {e | ∃ x y, ∀ G ∈ Gs, G.IsLink e x y} else ∅ := by
  simp only [sInf, ExtendedGraph, coe_injective.preimage_image]
  split_ifs with hne <;> rfl

@[simp]
lemma edgeSet_sInf_of_nonempty {Gs : Set (Graph α β)} (hGsne : Gs.Nonempty) :
    E(sInf Gs) = {e | ∃ x y, ∀ G ∈ Gs, G.IsLink e x y} := by
  classical
  grind

@[grind =]
lemma sInf_isLink (Gs : Set (Graph α β)) [Decidable Gs.Nonempty] :
    (sInf Gs).IsLink e x y ↔ if Gs.Nonempty then ∀ G ∈ Gs, G.IsLink e x y else False := by
  simp only [sInf, ExtendedGraph, coe_injective.preimage_image]
  split_ifs with hne <;> rfl

@[simp]
lemma sInf_isLink_of_nonempty {Gs : Set (Graph α β)} (hGsne : Gs.Nonempty) :
    (sInf Gs).IsLink e x y ↔ ∀ G ∈ Gs, G.IsLink e x y := by
  classical
  grind

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

@[simp] lemma inf_vertexSet (G H : Graph α β) : V(G ⊓ H) = V(G) ∩ V(H) := rfl

lemma inf_edgeSet (G H : Graph α β) :
    E(G ⊓ H) = {e ∈ E(G) ∩ E(H) | ∀ x y, G.IsLink e x y ↔ H.IsLink e x y} := rfl

@[simp] lemma inf_isLink_iff : (G ⊓ H).IsLink e x y ↔ G.IsLink e x y ∧ H.IsLink e x y := Iff.rfl

@[simp] lemma sInf_pair (G H : Graph α β) : sInf {G, H} = G ⊓ H := by ext <;> simp

end Graph
