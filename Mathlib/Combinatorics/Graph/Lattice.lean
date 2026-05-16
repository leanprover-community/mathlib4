/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson, Jun Kwon
-/
module

public import Mathlib.Combinatorics.Graph.Subgraph

/-!
# Intersection and union of graphs

This file defines the lattice-like structures on graphs.

## Main results

- `SemilatticeInf (Graph α β)`
- `Max (Graph α β)`
- `compatible_iff_le_le`

## Implementation notes

Intersections are defined here as the maximal mutual subgraph of the given graphs.
This has the effect of, when taking the intersection of non-compatible graphs,
**any non-compatible edges are removed**.

Union is defined here as left-preferred, meaning that any non-compatible edges
**follow the incidence in the left graph**. The union of non-compatible graphs unfortuantely does
not form a semilattice. The left-preference retains associativity at the cost of commutativity.

## TODO

+ Add `ConditionallyCompleteCompleteLatticeInf (Graph α β)` after splitting
  `ConditionallyCompleteCompleteLattice`.

-/

public section

open Function Set

variable {α β : Type*} {x y : α} {e : β} {G G' H : Graph α β}

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
protected lemma disjoint_iff : Disjoint G H ↔ Disjoint V(G) V(H) := by
  rw [disjoint_iff, ← vertexSet_eq_empty_iff, vertexSet_inf, disjoint_iff_inter_eq_empty]

protected lemma Compatible.edgeSet_inf (h : G.Compatible H) : E(G ⊓ H) = E(G) ∩ E(H) := by
  rw [G.edgeSet_inf]
  exact le_antisymm (fun e he ↦ he.1) fun e he ↦ ⟨he, fun _ _ ↦ h.isLink_congr he.1 he.2⟩

lemma inf_isInducedSubgraph (h : G ≤i H) (h' : G' ≤i H) : G ⊓ G' ≤i H where
  le := inf_le_left.trans <| show G ≤ H by exact h.le
  isLink_of_mem_mem _ _ _ hxy hx hy := by
    simp [h.isLink_of_mem_mem hxy hx.1 hy.1, h'.isLink_of_mem_mem hxy hx.2 hy.2]

lemma inf_isSpanningSubgraph (h : G ≤s H) (h' : G' ≤s H) : G ⊓ G' ≤s H where
  le := inf_le_left.trans <| show G ≤ H by exact h.le
  vertexSet_eq := by simp [h.vertexSet_eq, h'.vertexSet_eq]

lemma inf_isClosedSubgraph (h : G ≤c H) (h' : G' ≤c H) : G ⊓ G' ≤c H where
  isInducedSubgraph := inf_isInducedSubgraph h.isInducedSubgraph h'.isInducedSubgraph
  closed _ _ he hx := by
    simp [h.closed he hx.1, h'.closed he hx.2, Compatible.of_le_le h.le h'.le |>.edgeSet_inf]

/-- Left-preferred sup of two graphs `G` and `H`. For any incompatible edges, incidence in the
left graph is used in the sup. Due to incompatibility, this does not form a semilattice.
Left-preference retains associativity at the cost of commutativity. -/
instance : Max (Graph α β) where
  max G H := {
    vertexSet := V(G) ∪ V(H)
    edgeSet := E(G) ∪ E(H)
    IsLink e x y := G.IsLink e x y ∨ e ∉ E(G) ∧ H.IsLink e x y
    isLink_symm _ _ _ _ h := by grind [G.isLink_comm, H.isLink_comm]
    eq_or_eq_of_isLink_of_isLink e _ _ _ _ h h' := by
      by_cases he : e ∈ E(G) <;> grind [eq_or_eq_of_isLink_of_isLink, IsLink.edge_mem]
    edge_mem_iff_exists_isLink e := by
      refine ⟨fun h ↦ ?_, fun ⟨x, y, he⟩ ↦ by grind [IsLink.edge_mem]⟩
      by_cases he : e ∈ E(G) <;> [obtain ⟨x, y, he⟩ := exists_isLink_of_mem_edgeSet he;
        obtain ⟨x, y, he⟩ := exists_isLink_of_mem_edgeSet <| h.resolve_left he] <;> grind}

@[simp, grind =]
lemma sup_vertexSet (G H : Graph α β) : V(G ⊔ H) = V(G) ∪ V(H) := rfl

@[simp, grind =]
lemma sup_edgeSet (G H : Graph α β) : E(G ⊔ H) = E(G) ∪ E(H) := rfl

@[grind =]
lemma sup_isLink : (G ⊔ H).IsLink e x y ↔ G.IsLink e x y ∨ (e ∉ E(G) ∧ H.IsLink e x y) := Iff.rfl

@[simp] protected lemma left_le_sup (G H : Graph α β) : G ≤ G ⊔ H := by constructor <;> grind

protected lemma sup_le (h : G ≤ H) (h' : G' ≤ H) : G ⊔ G' ≤ H where
  vertexSet_mono := by grind [h.vertexSet_mono, h'.vertexSet_mono]
  isLink_mono := by grind [h.isLink_mono, h'.isLink_mono]

@[simp]
protected lemma sup_self (G : Graph α β) : G ⊔ G = G :=
  (Graph.sup_le le_rfl le_rfl).antisymm <| Graph.left_le_sup ..

protected lemma sup_assoc (G₁ G₂ G₃ : Graph α β) : (G₁ ⊔ G₂) ⊔ G₃ = G₁ ⊔ (G₂ ⊔ G₃) := by
  refine Graph.ext (Set.union_assoc ..) fun e x y ↦ ?_
  simp [sup_isLink]
  tauto

instance : Std.Associative (α := Graph α β) (· ⊔ ·) where
  assoc := Graph.sup_assoc

lemma Compatible.sup_isLink (h : G.Compatible H) :
    (G ⊔ H).IsLink e x y ↔ G.IsLink e x y ∨ H.IsLink e x y := by
  by_cases heG : e ∈ E(G)
  · simp only [Graph.sup_isLink, heG, not_true_eq_false, false_and, or_false, iff_self_or]
    exact fun he ↦ by rwa [h.isLink_congr heG he.edge_mem]
  simp [heG, Graph.sup_isLink]

lemma Compatible.sup_comm (h : Compatible G H) : G ⊔ H = H ⊔ G :=
  Graph.ext (Set.union_comm ..) fun _ _ _ ↦ by rw [h.sup_isLink, h.symm.sup_isLink, or_comm]

lemma Compatible.right_le_sup (h : G.Compatible H) : H ≤ G ⊔ H := by
  simp [h.sup_comm]

lemma Compatible.sup_le_iff (hc : G.Compatible G') : G ⊔ G' ≤ H ↔ G ≤ H ∧ G' ≤ H :=
  ⟨fun h ↦ ⟨G.left_le_sup _ |>.trans h, hc.right_le_sup.trans h⟩, fun ⟨hG, hG'⟩ ↦ G.sup_le hG hG'⟩

/-- Two graphs are compatible if and only if they have a common supergraph. This shows that
  arbitrary unions of graphs are well-behaved under `BddAbove`. -/
lemma compatible_iff_le_le : G.Compatible G' ↔ ∃ H, G ≤ H ∧ G' ≤ H :=
  ⟨fun h ↦ ⟨G ⊔ G', G.left_le_sup _, h.right_le_sup⟩,
    fun ⟨_, hG, hG'⟩ ↦ Compatible.of_le_le hG hG'⟩

end Graph
