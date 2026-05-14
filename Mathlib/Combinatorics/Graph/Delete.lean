/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson, Jun Kwon
-/
module

public import Mathlib.Combinatorics.Graph.Subgraph
import Mathlib.Data.Finset.Attr
import Mathlib.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

/-!
# Deletion of edges and vertices

This file defines the deletion of edges and vertices from a graph.

## Main definitions

- `restrict`: the subgraph of `G` restricted to the edges in `F` without
  removing vertices
- `deleteEdges`: the subgraph of `G` with the edges in `F` deleted
- `induce`: the subgraph of `G` induced by the set `X` of vertices
- `deleteVerts` : the graph obtained from `G` by deleting the set `X` of vertices

## Tags

graphs, edge deletion, vertex deletion
-/

public section

variable {α β : Type*} {x y : α} {e : β} {G H : Graph α β} {F F₀ : Set β} {X : Set α}

open Set Function

namespace Graph

/-- Restrict `G : Graph α β` to the edges in a set `E₀` without removing vertices -/
@[expose, simps (attr := grind =)]
def restrict (G : Graph α β) (E₀ : Set β) : Graph α β where
  vertexSet := V(G)
  edgeSet := E(G) ∩ E₀
  IsLink e x y := e ∈ E₀ ∧ G.IsLink e x y
  isLink_symm e he x y h := ⟨h.1, h.2.symm⟩
  eq_or_eq_of_isLink_of_isLink _ _ _ _ _ h h' := h.2.left_eq_or_eq h'.2
  edge_mem_iff_exists_isLink e := ⟨fun h ↦ by simp [G.exists_isLink_of_mem_edgeSet h.1, h.2],
    fun ⟨x, y, h⟩ ↦ ⟨h.2.edge_mem, h.1⟩⟩

@[simp]
lemma restrict_le {E₀ : Set β} : G.restrict E₀ ≤ G where
  vertexSet_mono := le_rfl
  isLink_mono := by simp

@[simp]
lemma restrict_eq_self_iff (G : Graph α β) (E₀ : Set β) : G.restrict E₀ = G ↔ E(G) ⊆ E₀ :=
  ⟨fun h ↦ by simpa using h.ge.edgeSet_mono,
    fun h ↦ (Compatible.of_le restrict_le).ext (by simp) (by simpa)⟩

@[simp]
lemma restrict_self (G : Graph α β) : G.restrict E(G) = G :=
  (Compatible.of_le_le (G := G) (by simp) (by simp)).ext rfl (by simp)

@[simp]
lemma restrict_edgeSet_inter (G : Graph α β) (F : Set β) : G.restrict (E(G) ∩ F) = G.restrict F :=
  (Compatible.of_le_le (G := G) (by simp) (by simp)).ext (by simp) (by simp)

@[simp]
lemma restrict_inter_edgeSet (G : Graph α β) (F : Set β) :
    G.restrict (F ∩ E(G)) = G.restrict F := by
  rw [inter_comm, restrict_edgeSet_inter]

@[gcongr]
lemma restrict_mono_left (h : H ≤ G) (F : Set β) : H.restrict F ≤ G.restrict F := by
  refine (Compatible.of_le_le (G := G) (restrict_le.trans h) (by simp)).le_iff.mpr ⟨?_, ?_⟩
  · simpa using h.vertexSet_mono
  simp [inter_subset_left.trans h.edgeSet_mono]

@[gcongr]
lemma restrict_mono_right (G : Graph α β) (hss : F₀ ⊆ F) : G.restrict F₀ ≤ G.restrict F where
  vertexSet_mono := subset_rfl
  isLink_mono _ _ _ := fun h ↦ ⟨hss h.1, h.2⟩

@[simp, grind =]
lemma restrict_inc : (G.restrict F).Inc e x ↔ G.Inc e x ∧ e ∈ F := by
  simp [Inc, and_comm]

@[simp, grind =]
lemma restrict_isLoopAt : (G.restrict F).IsLoopAt e x ↔ G.IsLoopAt e x ∧ e ∈ F := by
  simp [← isLink_self_iff, and_comm]

@[simp]
lemma restrict_restrict (G : Graph α β) (F₁ F₂ : Set β) :
    (G.restrict F₁).restrict F₂ = G.restrict (F₁ ∩ F₂) := by
  refine (Compatible.of_le_le (G := G) (restrict_le.trans (by simp)) (by simp)).ext (by simp) ?_
  simp only [edgeSet_restrict]
  rw [← inter_assoc, inter_comm _ F₂]

/-- Delete a set `F` of edges from `G`. This is a special case of `restrict`,
but we define it with `copy` so that the edge set is definitionally equal to `E(G) \ F`. -/
@[expose, simps! (attr := grind =)]
def deleteEdges (G : Graph α β) (F : Set β) : Graph α β :=
  (G.restrict (E(G) \ F)).copy (edgeSet := E(G) \ F)
  (IsLink := fun e x y ↦ G.IsLink e x y ∧ e ∉ F) rfl (by simp)
  (fun e x y ↦ by
    simp only [restrict_isLink, mem_diff, and_comm, and_congr_left_iff, and_iff_left_iff_imp]
    exact fun h _ ↦ h.edge_mem)

@[simp]
lemma restrict_edgeSet_diff_eq_deleteEdges (G : Graph α β) (F : Set β) :
    G.restrict (E(G) \ F) = G.deleteEdges F := copy_eq .. |>.symm

@[simp]
lemma deleteEdges_le : G.deleteEdges F ≤ G := by
  simp [← restrict_edgeSet_diff_eq_deleteEdges]

lemma restrict_eq_deleteEdges (G : Graph α β) (F : Set β) :
    G.restrict F = G.deleteEdges (E(G) \ F) :=
  (Compatible.of_le_le restrict_le deleteEdges_le).ext rfl (by simp)

@[simp, grind =]
lemma deleteEdges_empty : G.deleteEdges ∅ = G := by
  simp [← restrict_edgeSet_diff_eq_deleteEdges]

@[gcongr]
lemma deleteEdges_mono_left (h : H ≤ G) (F : Set β) : H.deleteEdges F ≤ G.deleteEdges F := by
  simp_rw [← restrict_edgeSet_diff_eq_deleteEdges]
  refine (restrict_mono_left h (E(H) \ F)).trans (G.restrict_mono_right ?_)
  exact diff_subset_diff_left h.edgeSet_mono

@[simp, grind =]
lemma deleteEdges_inc : (G.deleteEdges F).Inc e x ↔ G.Inc e x ∧ e ∉ F := by
  simp [Inc, and_comm]

@[simp, grind =]
lemma deleteEdges_isLoopAt : (G.deleteEdges F).IsLoopAt e x ↔ G.IsLoopAt e x ∧ e ∉ F := by
  simp only [← restrict_edgeSet_diff_eq_deleteEdges, restrict_isLoopAt, mem_diff,
    and_congr_right_iff, and_iff_right_iff_imp]
  exact fun h _ ↦ h.edge_mem

@[simp]
lemma deleteEdges_deleteEdges (G : Graph α β) (F₁ F₂ : Set β) :
    (G.deleteEdges F₁).deleteEdges F₂ = G.deleteEdges (F₁ ∪ F₂) := by
  simp only [← restrict_edgeSet_diff_eq_deleteEdges, diff_eq_compl_inter, restrict_inter_edgeSet,
    edgeSet_restrict, restrict_restrict, compl_union]
  rw [← inter_comm, inter_comm F₁ᶜ, inter_assoc, inter_assoc, inter_self, inter_comm,
    inter_assoc, inter_comm, restrict_inter_edgeSet, inter_comm]

/-- The subgraph of `G` induced by a set `X` of vertices.
The edges are the edges of `G` with both ends in `X`.
(`X` is not required to be a subset of `V(G)` for this definition to work,
even though this is the standard use case) -/
@[expose, simps! (attr := grind =) vertexSet isLink]
protected def induce (G : Graph α β) (X : Set α) : Graph α β where
  vertexSet := X
  IsLink e x y := G.IsLink e x y ∧ x ∈ X ∧ y ∈ X
  isLink_symm _ _ x := by simp +contextual [G.isLink_comm (x := x)]
  eq_or_eq_of_isLink_of_isLink _ _ _ _ _ h h' := h.1.left_eq_or_eq h'.1

lemma induce_le (hX : X ⊆ V(G)) : G.induce X ≤ G := ⟨hX, fun _ _ _ h ↦ h.1⟩

@[simp, grind =]
lemma induce_le_iff : G.induce X ≤ G ↔ X ⊆ V(G) := ⟨(·.vertexSet_mono), induce_le⟩

lemma edgeSet_induce (G : Graph α β) (X : Set α) :
    E(G.induce X) = {e | ∃ x y, G.IsLink e x y ∧ x ∈ X ∧ y ∈ X} := rfl

@[simp, grind =]
lemma induce_vertexSet (G : Graph α β) : G.induce V(G) = G := by
  refine (Compatible.of_le_le (G := G) (by simp) (by simp)).ext rfl <| Set.ext fun e ↦
    ⟨fun ⟨_, _, h⟩ ↦ h.1.edge_mem, fun h ↦ ?_⟩
  obtain ⟨x, y, h⟩ := exists_isLink_of_mem_edgeSet h
  exact ⟨x, y, h, h.left_mem, h.right_mem⟩

/-- The graph obtained from `G` by deleting a set of vertices. -/
def deleteVerts (G : Graph α β) (X : Set α) : Graph α β := G.induce (V(G) \ X)

@[simp, grind =]
lemma vertexSet_deleteVerts (G : Graph α β) (X : Set α) : V(G.deleteVerts X) = V(G) \ X := by
  unfold deleteVerts
  rfl

@[simp, grind =]
lemma deleteVerts_isLink (G : Graph α β) (X : Set α) :
    (G.deleteVerts X).IsLink e x y ↔ (G.IsLink e x y ∧ x ∉ X ∧ y ∉ X) := by
  simp only [deleteVerts, induce_isLink, mem_diff, and_congr_right_iff]
  exact fun h ↦ by simp [h.left_mem, h.right_mem]

@[simp]
lemma edgeSet_deleteVerts (G : Graph α β) (X : Set α) :
    E(G.deleteVerts X) = {e | ∃ x y, G.IsLink e x y ∧ x ∉ X ∧ y ∉ X} := by
  simp [edgeSet_eq_setOf_exists_isLink]

@[simp, grind =]
lemma deleteVerts_empty (G : Graph α β) : G.deleteVerts (∅ : Set α) = G := by
  simp [deleteVerts]

@[simp] lemma deleteVerts_le : G.deleteVerts X ≤ G := G.induce_le diff_subset

end Graph
