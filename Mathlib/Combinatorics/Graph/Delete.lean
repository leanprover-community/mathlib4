/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson, Jun Kwon
-/
module

public import Mathlib.Combinatorics.Graph.Subgraph

/-!
# Deletion of edges and vertices

This file defines the deletion of edges and vertices from a graph.

## Main definitions

- `G ↾ F` (`Graph.edgeRestrict`) : the subgraph of `G` restricted to the edges in `F` without
removing vertices
- `G ＼ F` (`Graph.edgeDelete`) : the subgraph of `G` with the edges in `F` deleted
- `G[X]` (`Graph.induce`) : the subgraph of `G` induced by the set `X` of vertices
- `G - X` (`Graph.vertexDelete`) : the graph obtained from `G` by deleting the set `X` of vertices

## Tags

graphs, edge deletion, vertex deletion
-/

@[expose] public section

variable {α β : Type*} {x y : α} {e : β} {G H : Graph α β} {F F₀ : Set β} {X : Set α}

open Set Function

namespace Graph

/-- Restrict `G : Graph α β` to the edges in a set `E₀` without removing vertices -/
@[simps (attr := grind =)]
def edgeRestrict (G : Graph α β) (E₀ : Set β) : Graph α β where
  vertexSet := V(G)
  edgeSet := E(G) ∩ E₀
  IsLink e x y := e ∈ E₀ ∧ G.IsLink e x y
  isLink_symm e he x y h := ⟨h.1, h.2.symm⟩
  eq_or_eq_of_isLink_of_isLink _ _ _ _ _ h h' := h.2.left_eq_or_eq h'.2
  edge_mem_iff_exists_isLink e := ⟨fun h ↦ by simp [G.exists_isLink_of_mem_edgeSet h.1, h.2],
    fun ⟨x, y, h⟩ ↦ ⟨h.2.edge_mem, h.1⟩⟩
  left_mem_of_isLink _ _ _ h := h.2.left_mem

@[inherit_doc edgeRestrict]
scoped infixl:65 " ↾ "  => Graph.edgeRestrict

@[simp]
lemma edgeRestrict_le {E₀ : Set β} : G ↾ E₀ ≤ G where
  vertexSet_mono := rfl.le
  isLink_mono := by simp

@[simp]
lemma edgeRestrict_eq_self_iff (G : Graph α β) (E₀ : Set β) : G ↾ E₀ = G ↔ E(G) ⊆ E₀ :=
  ⟨fun h ↦ by simpa using h.ge.edgeSet_mono,
    fun h ↦ (Compatible.of_le edgeRestrict_le).ext (by simp) (by simpa)⟩

@[simp]
lemma edgeRestrict_self (G : Graph α β) : G ↾ E(G) = G :=
  (Compatible.of_le_le (G := G) (by simp) (by simp)).ext rfl (by simp)

@[simp]
lemma edgeRestrict_edgeSet_inter (G : Graph α β) (F : Set β) : G ↾ (E(G) ∩ F) = G ↾ F :=
  (Compatible.of_le_le (G := G) (by simp) (by simp)).ext (by simp) (by simp)

@[simp]
lemma edgeRestrict_inter_edgeSet (G : Graph α β) (F : Set β) : G ↾ (F ∩ E(G)) = G ↾ F := by
  rw [inter_comm, edgeRestrict_edgeSet_inter]

@[gcongr]
lemma edgeRestrict_mono_left (h : H ≤ G) (F : Set β) : H ↾ F ≤ G ↾ F := by
  refine (Compatible.of_le_le (G := G) (edgeRestrict_le.trans h) (by simp)).le_iff.mpr ⟨?_, ?_⟩
  · simpa using h.vertexSet_mono
  simp [inter_subset_left.trans h.edgeSet_mono]

@[gcongr]
lemma edgeRestrict_mono_right (G : Graph α β) (hss : F₀ ⊆ F) : G ↾ F₀ ≤ G ↾ F where
  vertexSet_mono := subset_rfl
  isLink_mono _ _ _ := fun h ↦ ⟨hss h.1, h.2⟩

@[simp, grind =]
lemma edgeRestrict_inc : (G ↾ F).Inc e x ↔ G.Inc e x ∧ e ∈ F := by
  simp [Inc, and_comm]

@[simp, grind =]
lemma edgeRestrict_isLoopAt : (G ↾ F).IsLoopAt e x ↔ G.IsLoopAt e x ∧ e ∈ F := by
  simp [← isLink_self_iff, and_comm]

@[simp]
lemma edgeRestrict_edgeRestrict (G : Graph α β) (F₁ F₂ : Set β) : (G ↾ F₁) ↾ F₂ = G ↾ F₁ ∩ F₂ := by
  refine (Compatible.of_le_le (G := G) (edgeRestrict_le.trans (by simp)) (by simp)).ext (by simp) ?_
  simp only [edgeRestrict_edgeSet]
  rw [← inter_assoc, inter_comm _ F₂]

/-- Delete a set `F` of edges from `G`. This is a special case of `edgeRestrict`,
but we define it with `copy` so that the edge set is definitionally equal to `E(G) \ F`. -/
@[simps! (attr := grind =)]
def edgeDelete (G : Graph α β) (F : Set β) : Graph α β :=
  (G.edgeRestrict (E(G) \ F)).copy (edgeSet := E(G) \ F)
  (IsLink := fun e x y ↦ G.IsLink e x y ∧ e ∉ F) rfl (by simp)
  (fun e x y ↦ by
    simp only [edgeRestrict_isLink, mem_diff, and_comm, and_congr_left_iff, and_iff_left_iff_imp]
    exact fun h _ ↦ h.edge_mem)

@[inherit_doc edgeDelete]
scoped infixl:75 " ＼ "  => Graph.edgeDelete

lemma edgeDelete_eq_edgeRestrict (G : Graph α β) (F : Set β) : G ＼ F = G ↾ (E(G) \ F) := copy_eq ..

@[simp]
lemma edgeDelete_le : G ＼ F ≤ G := by
  simp [edgeDelete_eq_edgeRestrict]

lemma edgeRestrict_eq_edgeDelete (G : Graph α β) (F : Set β) : G ↾ F = G ＼ (E(G) \ F) :=
  (Compatible.of_le_le edgeRestrict_le edgeDelete_le).ext rfl (by simp)

@[simp, grind =]
lemma edgeDelete_empty : G ＼ ∅ = G := by
  simp [edgeDelete_eq_edgeRestrict]

@[gcongr]
lemma edgeDelete_mono_left (h : H ≤ G) (F : Set β) : H ＼ F ≤ G ＼ F := by
  simp_rw [edgeDelete_eq_edgeRestrict]
  refine (edgeRestrict_mono_left h (E(H) \ F)).trans (G.edgeRestrict_mono_right ?_)
  exact diff_subset_diff_left h.edgeSet_mono

@[simp, grind =]
lemma edgeDelete_inc : (G ＼ F).Inc e x ↔ G.Inc e x ∧ e ∉ F := by
  simp [Inc, and_comm]

@[simp, grind =]
lemma edgeDelete_isLoopAt : (G ＼ F).IsLoopAt e x ↔ G.IsLoopAt e x ∧ e ∉ F := by
  simp only [edgeDelete_eq_edgeRestrict, edgeRestrict_isLoopAt, mem_diff, and_congr_right_iff,
    and_iff_right_iff_imp]
  exact fun h _ ↦ h.edge_mem

@[simp]
lemma edgeDelete_edgeDelete (G : Graph α β) (F₁ F₂ : Set β) : G ＼ F₁ ＼ F₂ = G ＼ (F₁ ∪ F₂) := by
  simp only [edgeDelete_eq_edgeRestrict, diff_eq_compl_inter, edgeRestrict_inter_edgeSet,
    edgeRestrict_edgeSet, edgeRestrict_edgeRestrict, compl_union]
  rw [← inter_comm, inter_comm F₁ᶜ, inter_assoc, inter_assoc, inter_self, inter_comm,
    inter_assoc, inter_comm, edgeRestrict_inter_edgeSet, inter_comm]

/-- The subgraph of `G` induced by a set `X` of vertices.
The edges are the edges of `G` with both ends in `X`.
(`X` is not required to be a subset of `V(G)` for this definition to work,
even though this is the standard use case) -/
@[simps! (attr := grind =) vertexSet isLink]
protected def induce (G : Graph α β) (X : Set α) : Graph α β where
  vertexSet := X
  IsLink e x y := G.IsLink e x y ∧ x ∈ X ∧ y ∈ X
  isLink_symm _ _ x := by simp +contextual [G.isLink_comm (x := x)]
  eq_or_eq_of_isLink_of_isLink _ _ _ _ _ h h' := h.1.left_eq_or_eq h'.1
  left_mem_of_isLink := by simp +contextual

@[inherit_doc Graph.induce]
scoped notation G "[" X "]" => Graph.induce G X

lemma induce_le (hX : X ⊆ V(G)) : G[X] ≤ G := ⟨hX, fun _ _ _ h ↦ h.1⟩

@[simp, grind =]
lemma induce_le_iff : G[X] ≤ G ↔ X ⊆ V(G) := ⟨(·.vertexSet_mono), induce_le⟩

lemma edgeSet_induce (G : Graph α β) (X : Set α) :
    E(G[X]) = {e | ∃ x y, G.IsLink e x y ∧ x ∈ X ∧ y ∈ X} := rfl

@[simp, grind =]
lemma induce_vertexSet_self (G : Graph α β) : G[V(G)] = G := by
  refine (Compatible.of_le_le (G := G) (by simp) (by simp)).ext rfl <| Set.ext fun e ↦
    ⟨fun ⟨_, _, h⟩ ↦ h.1.edge_mem, fun h ↦ ?_⟩
  obtain ⟨x, y, h⟩ := exists_isLink_of_mem_edgeSet h
  exact ⟨x, y, h, h.left_mem, h.right_mem⟩

/-- The graph obtained from `G` by deleting a set of vertices. -/
def vertexDelete (G : Graph α β) (X : Set α) : Graph α β := G[V(G) \ X]

@[inherit_doc vertexDelete]
instance : HSub (Graph α β) (Set α) (Graph α β) where
  hSub G X := G[V(G) \ X]

lemma vertexDelete_def (G : Graph α β) (X : Set α) : G - X = G [V(G) \ X] := rfl

@[simp, grind =]
lemma vertexDelete_vertexSet (G : Graph α β) (X : Set α) : V(G - X) = V(G) \ X := rfl

@[simp, grind =]
lemma vertexDelete_isLink (G : Graph α β) (X : Set α) :
    (G - X).IsLink e x y ↔ (G.IsLink e x y ∧ x ∉ X ∧ y ∉ X) := by
  simp only [vertexDelete_def, induce_isLink, mem_diff, and_congr_right_iff]
  exact fun h ↦ by simp [h.left_mem, h.right_mem]

@[simp]
lemma vertexDelete_edgeSet (G : Graph α β) (X : Set α) :
    E(G - X) = {e | ∃ x y, G.IsLink e x y ∧ x ∉ X ∧ y ∉ X} := by
  simp [edgeSet_eq_setOf_exists_isLink]

@[simp, grind =]
lemma vertexDelete_empty (G : Graph α β) : G - (∅ : Set α) = G := by
  simp [vertexDelete_def]

@[simp]
lemma vertexDelete_le : G - X ≤ G := G.induce_le diff_subset

end Graph
