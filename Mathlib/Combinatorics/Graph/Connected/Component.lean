/-
Copyright (c) 2025 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson, Jun Kwon
-/
module

public import Mathlib.Order.Minimal
public import Mathlib.Combinatorics.Graph.Subgraph

/-!
# Connected components of graphs

This file defines the connected components and connectedness of a graph.

## Main definitions

* `IsCompOf`: a graph `H` is a component of `G` if it is a minimal nonempty closed subgraph of `G`.
* `IsConnected`: a graph `G` is connected if it is a component of itself. Empty graph is not
  considered connected.

-/

public section

variable {α β : Type*} {G H K : Graph α β}

namespace Graph

/-! ### Components -/

/-- A component of `G` is a minimal nonempty closed subgraph of `G`. -/
@[expose] def IsCompOf (H G : Graph α β) : Prop := Minimal (fun H ↦ H ≤c G ∧ V(H).Nonempty) H

namespace IsCompOf

@[simp] lemma isClosedSubgraph (h : H.IsCompOf G) : H ≤c G := h.prop.1
lemma isInducedSubgraph (h : H.IsCompOf G) : H ≤i G := h.isClosedSubgraph.isInducedSubgraph
@[simp] lemma le (h : H.IsCompOf G) : H ≤ G := h.isClosedSubgraph.le
@[simp, grind →] lemma nonempty (h : H.IsCompOf G) : V(H).Nonempty := h.prop.2

lemma anti_right (hKH : K ≤ H) (hHG : H ≤ G) (h : K.IsCompOf G) : K.IsCompOf H :=
  ⟨⟨h.isClosedSubgraph.anti_right hKH hHG, h.nonempty⟩, fun _ ⟨hK'H, hK'ne⟩ hK'K ↦
    h.le_of_le ⟨(hK'H.anti_right hK'K hKH).trans h.isClosedSubgraph, hK'ne⟩ hK'K⟩

end IsCompOf

/-! ### Connectedness -/

/-- A graph is connected if it is a minimal closed subgraph of itself. -/
protected def IsConnected (G : Graph α β) : Prop := G.IsCompOf G

lemma IsConnected.nonempty (hG : G.IsConnected) : V(G).Nonempty := IsCompOf.nonempty hG

@[simp]
lemma IsConnected.bot_not_isConnected : ¬ (⊥ : Graph α β).IsConnected := by
  rintro h
  simpa using h.nonempty

lemma isConnected_iff_forall_closed (hG : V(G).Nonempty) :
    G.IsConnected ↔ ∀ ⦃H⦄, H ≤c G → V(H).Nonempty → H = G := by
  refine ⟨fun h H hHG hHne ↦ ?_, fun h ↦ ⟨by simpa, fun H ⟨hle, hH⟩ _ ↦ (h hle hH).symm.le⟩⟩
  rw [Graph.IsConnected] at h
  exact h.eq_of_le ⟨hHG, hHne⟩ hHG.le

lemma isConnected_iff_forall_closed_ge (hG : V(G).Nonempty) :
    G.IsConnected ↔ ∀ ⦃H⦄, H ≤c G → V(H).Nonempty → G ≤ H := by
  rw [isConnected_iff_forall_closed hG]
  exact ⟨fun h H hle hne ↦ (h hle hne).symm.le, fun h H hle hne ↦ (h hle hne).antisymm' hle.le⟩

lemma IsConnected.ext_of_isClosedSubgraph (hH : H ≤c G) (hne : V(H).Nonempty) (hG : G.IsConnected) :
    H = G := by
  rw [isConnected_iff_forall_closed (hne.mono hH.le.vertexSet_mono)] at hG
  exact hG hH hne

lemma IsCompOf.isConnected (h : H.IsCompOf G) : H.IsConnected := h.anti_right le_rfl h.le

lemma IsConnected.exists_inc_notMem_of_lt (hlt : H < G) (hne : V(H).Nonempty) (hG : G.IsConnected) :
    ∃ e x, G.Inc e x ∧ e ∉ E(H) ∧ x ∈ V(H) := by
  refine by_contra fun hcon ↦ hlt.ne <| hG.ext_of_isClosedSubgraph ?_ hne
  refine IsClosedSubgraph.mk' hlt.le fun e x hex hx ↦ ?_
  simp only [not_exists, not_and, not_imp_not] at hcon
  exact hcon _ _ hex hx

end Graph
