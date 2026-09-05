/-
Copyright (c) 2026 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson, Jun Kwon
-/
module

public import Mathlib.Order.Minimal
public import Mathlib.Combinatorics.Graph.Subgraph

/-!
# Connected components of graphs

This file defines predicate for being a connected component of a graph and the notion of a
connected graph.

## Main definitions

* `IsConnectedComponentOf H G`: `H` is a connected component of `G` if `H` is a minimal nonempty
  closed subgraph of `G`.
* `Connected G`: `G` is connected if `G` is a connected component of itself. In particular, the
  empty graph is not connected.

-/

public section

variable {α β : Type*} {G H K : Graph α β}

namespace Graph

/-! ### Connected components -/

/-- A connected component of `G` is a minimal nonempty closed subgraph of `G`. -/
@[expose] def IsConnectedComponentOf (H G : Graph α β) : Prop :=
  Minimal (fun H ↦ H ≤c G ∧ V(H).Nonempty) H

namespace IsConnectedComponentOf

@[simp] lemma isClosedSubgraph (h : H.IsConnectedComponentOf G) : H ≤c G := h.prop.1
lemma isInducedSubgraph (h : H.IsConnectedComponentOf G) : H ≤i G :=
  h.isClosedSubgraph.isInducedSubgraph
@[simp] lemma le (h : H.IsConnectedComponentOf G) : H ≤ G := h.isClosedSubgraph.le
@[grind →] lemma nonempty (h : H.IsConnectedComponentOf G) : V(H).Nonempty := h.prop.2

lemma anti_right (hKH : K ≤ H) (hHG : H ≤ G) (h : K.IsConnectedComponentOf G) :
    K.IsConnectedComponentOf H :=
  ⟨⟨h.isClosedSubgraph.anti_right hKH hHG, h.nonempty⟩, fun _ ⟨hK'H, hK'ne⟩ hK'K ↦
    h.le_of_le ⟨(hK'H.anti_right hK'K hKH).trans h.isClosedSubgraph, hK'ne⟩ hK'K⟩

end IsConnectedComponentOf

/-! ### Connectedness -/

/-- A graph is connected if it is a connected component of itself (`G.IsConnectedComponentOf G`). -/
@[expose] protected def Connected (G : Graph α β) : Prop := G.IsConnectedComponentOf G

lemma Connected.nonempty (hG : G.Connected) : V(G).Nonempty := IsConnectedComponentOf.nonempty hG

@[simp]
lemma not_connected_bot : ¬ (⊥ : Graph α β).Connected := by
  rintro h
  simpa using h.nonempty

lemma connected_iff_forall_closed (hG : V(G).Nonempty) :
    G.Connected ↔ ∀ ⦃H⦄, H ≤c G → V(H).Nonempty → H = G := by
  refine ⟨fun h H hHG hHne ↦ ?_, fun h ↦ ⟨by simpa, fun H ⟨hle, hH⟩ _ ↦ (h hle hH).symm.le⟩⟩
  rw [Graph.Connected] at h
  exact h.eq_of_le ⟨hHG, hHne⟩ hHG.le

lemma connected_iff_forall_closed_ge (hG : V(G).Nonempty) :
    G.Connected ↔ ∀ ⦃H⦄, H ≤c G → V(H).Nonempty → G ≤ H := by
  rw [connected_iff_forall_closed hG]
  exact ⟨fun h H hle hne ↦ (h hle hne).symm.le, fun h H hle hne ↦ (h hle hne).antisymm' hle.le⟩

lemma Connected.ext_of_isClosedSubgraph (hH : H ≤c G) (hne : V(H).Nonempty) (hG : G.Connected) :
    H = G := by
  rw [connected_iff_forall_closed (hne.mono hH.le.vertexSet_mono)] at hG
  exact hG hH hne

lemma IsConnectedComponentOf.Connected (h : H.IsConnectedComponentOf G) : H.Connected :=
  h.anti_right le_rfl h.le

lemma Connected.exists_inc_notMem_of_lt (hlt : H < G) (hne : V(H).Nonempty) (hG : G.Connected) :
    ∃ e x, G.Inc e x ∧ e ∉ E(H) ∧ x ∈ V(H) := by
  refine by_contra fun hcon ↦ hlt.ne <| hG.ext_of_isClosedSubgraph ?_ hne
  refine IsClosedSubgraph.mk' hlt.le fun e x hex hx ↦ ?_
  simp only [not_exists, not_and, not_imp_not] at hcon
  exact hcon _ _ hex hx

end Graph
