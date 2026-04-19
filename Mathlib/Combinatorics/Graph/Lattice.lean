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

- `SemilatticeInf (Graph α β)`

## Implementation notes

Intersections are defined here as the maximal mutual subgraph of the given graphs.
This has the effect of, when taking the intersection of non-compatible graphs,
**any non-compatible edges are removed**.

## TODO

+ Add `ConditionallyCompleteCompleteLatticeInf (Graph α β)` after splitting
  `ConditionallyCompleteCompleteLattice`.

-/

public section

variable {α β ι : Type*} {x y : α} {e : β} {G G₁ G₂ H : Graph α β} {F F₀ : Set β} {X : Set α}
  {Gs : Set (Graph α β)} (Gι : ι → Graph α β) [Nonempty ι]

open Set Function

namespace Graph

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

@[simp]
lemma disjoint_iff : Disjoint G₁ G₂ ↔ Disjoint V(G₁) V(G₂) := by
  rw [disjoint_iff, ← vertexSet_eq_empty_iff, vertexSet_inf, disjoint_iff_inter_eq_empty]

protected lemma Compatible.edgeSet_inf (h : G.Compatible H) : E(G ⊓ H) = E(G) ∩ E(H) := by
  rw [G.edgeSet_inf]
  exact le_antisymm (fun e he ↦ he.1) fun e he ↦ ⟨he, fun _ _ ↦ h.isLink_congr he.1 he.2⟩

end Graph
