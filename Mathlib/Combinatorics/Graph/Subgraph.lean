/-
Copyright (c) 2025 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson, Jun Kwon
-/
import Mathlib.Combinatorics.Graph.Basic
import Mathlib.Tactic.TFAE
import Mathlib.Data.Set.BooleanAlgebra
import Mathlib.Order.OmegaCompletePartialOrder

/-!
# Basic relations and operations related to subgraphs

This file contains the basic theory of relations and operations related to subgraphs of graphs.

## Definitions

* `Graph.copy`
* `Graph.IsSubgraph`
* `Graph.edgeRestrict`
* `Graph.edgeDelete`
* `Graph.induce`
* `Graph.vertexDelete`
* `Graph.IsSpanningSubgraph`
* `Graph.IsInducedSubgraph`
* `Graph.IsClosedSubgraph`

-/

variable {α β : Type*} {x y z u v w : α} {e f : β} {G H K : Graph α β} {F F₁ F₂ : Set β}
    {X Y : Set α}

initialize_simps_projections Graph (IsLink → isLink)

open Set

open scoped Sym2

namespace Graph

/-- `Copy` creates an identical graph with different definitions for its vertex set and edge set.
  This is mainly used to create graphs with improved definitional properties. -/
@[simps]
def copy (G : Graph α β) {V : Set α} {E : Set β} {IsLink : β → α → α → Prop} (hV : V(G) = V)
    (hE : E(G) = E) (h_isLink : ∀ e x y, G.IsLink e x y ↔ IsLink e x y) : Graph α β where
  vertexSet := V
  edgeSet := E
  IsLink := IsLink
  isLink_symm e he x y := by
    simp_rw [← h_isLink]
    apply G.isLink_symm (hE ▸ he)
  eq_or_eq_of_isLink_of_isLink := by
    simp_rw [← h_isLink]
    exact G.eq_or_eq_of_isLink_of_isLink
  edge_mem_iff_exists_isLink := by
    simp_rw [← h_isLink, ← hE]
    exact G.edge_mem_iff_exists_isLink
  left_mem_of_isLink := by
    simp_rw [← h_isLink, ← hV]
    exact G.left_mem_of_isLink

lemma copy_eq_self (G : Graph α β) {V : Set α} {E : Set β} {IsLink : β → α → α → Prop}
    (hV : V(G) = V) (hE : E(G) = E) (h_isLink : ∀ e x y, G.IsLink e x y ↔ IsLink e x y) :
    G.copy hV hE h_isLink = G := by
  ext <;> simp_all

/-- `IsSubgraph H G` means that `V(H) ⊆ V(G)`, and every link in `H` is a link in `G`. -/
structure IsSubgraph (H G : Graph α β) : Prop where
  vertex_subset : V(H) ⊆ V(G)
  isLink_of_isLink : ∀ ⦃e x y⦄, H.IsLink e x y → G.IsLink e x y

/-- The subgraph order is a partial order on graphs. -/
instance : PartialOrder (Graph α β) where
  le := IsSubgraph
  le_refl _ := ⟨rfl.le, by simp⟩
  le_trans _ _ _ h₁ h₂ := ⟨h₁.1.trans h₂.1, fun _ _ _ h ↦ h₂.2 (h₁.2 h)⟩
  le_antisymm G H h₁ h₂ := Graph.ext (h₁.1.antisymm h₂.1)
    fun e x y ↦ ⟨fun a ↦ h₁.isLink_of_isLink a, fun a ↦ h₂.isLink_of_isLink a⟩

lemma IsLink.of_le (h : H.IsLink e x y) (hle : H ≤ G) : G.IsLink e x y :=
  hle.2 h

lemma IsLink.of_le_of_mem (h : G.IsLink e x y) (hle : H ≤ G) (he : e ∈ E(H)) : H.IsLink e x y := by
  obtain ⟨u, v, huv⟩ := exists_isLink_of_mem_edgeSet he
  obtain ⟨rfl, rfl⟩ | ⟨rfl,rfl⟩ := (huv.of_le hle).eq_and_eq_or_eq_and_eq h
  · assumption
  exact huv.symm

lemma Inc.of_le (h : H.Inc e x) (hle : H ≤ G) : G.Inc e x :=
  (h.choose_spec.of_le hle).inc_left

lemma Inc.of_le_of_mem (h : G.Inc e x) (hle : H ≤ G) (he : e ∈ E(H)) : H.Inc e x := by
  obtain ⟨y, hy⟩ := h
  exact (hy.of_le_of_mem hle he).inc_left

lemma IsLoopAt.of_le (h : H.IsLoopAt e x) (hle : H ≤ G) : G.IsLoopAt e x :=
  IsLink.of_le h hle

lemma IsNonloopAt.of_le (h : H.IsNonloopAt e x) (hle : H ≤ G) : G.IsNonloopAt e x := by
  obtain ⟨y, hxy, he⟩ := h
  exact ⟨y, hxy, he.of_le hle⟩

lemma Adj.of_le (h : H.Adj x y) (hle : H ≤ G) : G.Adj x y :=
  (h.choose_spec.of_le hle).adj

lemma vertexSet_mono (h : H ≤ G) : V(H) ⊆ V(G) :=
  h.1

lemma edgeSet_mono (h : H ≤ G) : E(H) ⊆ E(G) := by
  refine fun e he ↦ ?_
  obtain ⟨x, y, h'⟩ := exists_isLink_of_mem_edgeSet he
  exact (h'.of_le h).edge_mem

lemma le_iff : H ≤ G ↔ (V(H) ⊆ V(G)) ∧ ∀ ⦃e x y⦄, H.IsLink e x y → G.IsLink e x y :=
  ⟨fun h ↦ ⟨h.1, h.2⟩, fun h ↦ ⟨h.1, h.2⟩⟩

lemma isLink_iff_isLink_of_le_of_mem (hle : H ≤ G) (he : e ∈ E(H)) :
    G.IsLink e x y ↔ H.IsLink e x y :=
  ⟨fun h ↦ h.of_le_of_mem hle he, fun h ↦ h.of_le hle⟩

lemma le_of_le_le_subset_subset {H₁ H₂ : Graph α β} (h₁ : H₁ ≤ G) (h₂ : H₂ ≤ G) (hV : V(H₁) ⊆ V(H₂))
    (hE : E(H₁) ⊆ E(H₂)) : H₁ ≤ H₂ where
  vertex_subset := hV
  isLink_of_isLink e x y h := by
    rw [← G.isLink_iff_isLink_of_le_of_mem h₂ (hE h.edge_mem)]
    exact h.of_le h₁

lemma ext_of_le_le {H₁ H₂ : Graph α β} (h₁ : H₁ ≤ G) (h₂ : H₂ ≤ G) (hV : V(H₁) = V(H₂))
    (hE : E(H₁) = E(H₂)) : H₁ = H₂ :=
  (le_of_le_le_subset_subset h₁ h₂ hV.subset hE.subset).antisymm <|
    (le_of_le_le_subset_subset h₂ h₁ hV.symm.subset hE.symm.subset)

lemma isLink_eq_of_le (hle : H ≤ G) (he : e ∈ E(H)) : H.IsLink e = G.IsLink e := by
  ext x y
  exact ⟨fun h ↦ h.of_le hle, fun h ↦ h.of_le_of_mem hle he⟩

lemma isLink_eqOn_of_le (hle : H ≤ G) : EqOn H.IsLink G.IsLink E(H) :=
  fun _ ↦ isLink_eq_of_le hle

lemma inc_eq_of_le (hle : H ≤ G) (he : e ∈ E(H)) : H.Inc e = G.Inc e := by
  unfold Graph.Inc
  rw [isLink_eq_of_le hle he]

lemma inc_eqOn_of_le (hle : H ≤ G) : EqOn H.Inc G.Inc E(H) :=
  fun _ ↦ inc_eq_of_le hle

lemma isLoopAt_eq_of_le (hle : H ≤ G) (he : e ∈ E(H)) : H.IsLoopAt e = G.IsLoopAt e := by
  unfold Graph.IsLoopAt
  rw [isLink_eq_of_le hle he]

lemma isLoopAt_eqOn_of_le (hle : H ≤ G) : EqOn H.IsLoopAt G.IsLoopAt E(H) :=
  fun _ ↦ isLoopAt_eq_of_le hle

lemma isNonloopAt_eq_of_le (hle : H ≤ G) (he : e ∈ E(H)) : H.IsNonloopAt e = G.IsNonloopAt e := by
  unfold Graph.IsNonloopAt
  rw [isLink_eq_of_le hle he]

lemma isNonloopAt_eqOn_of_le (hle : H ≤ G) : EqOn H.IsNonloopAt G.IsNonloopAt E(H) :=
  fun _ ↦ isNonloopAt_eq_of_le hle

lemma vertexSet_ssubset_or_edgeSet_ssubset_of_lt (h : G < H) : V(G) ⊂ V(H) ∨ E(G) ⊂ E(H) := by
  rw [lt_iff_le_and_ne] at h
  simp only [ssubset_iff_subset_ne, vertexSet_mono h.1, ne_eq, true_and, edgeSet_mono h.1]
  by_contra! heq
  exact h.2 <| ext_of_le_le h.1 le_rfl heq.1 heq.2

/- TODO : Is is reasonable to only keep the `EqOn` versions of the above?
Also, what about functional `≤` versions? -/

/-- Restrict `G : Graph α β` to the edges in a set `E₀` without removing vertices -/
@[simps isLink]
def edgeRestrict (G : Graph α β) (E₀ : Set β) : Graph α β where
  vertexSet := V(G)
  edgeSet := E₀ ∩ E(G)
  IsLink e x y := e ∈ E₀ ∧ G.IsLink e x y
  isLink_symm e he x y h := ⟨h.1, h.2.symm⟩

  eq_or_eq_of_isLink_of_isLink _ _ _ _ _ h h' := h.2.left_eq_or_eq h'.2
  edge_mem_iff_exists_isLink e := ⟨fun h ↦ by simp [G.exists_isLink_of_mem_edgeSet h.2, h.1],
    fun ⟨x, y, h⟩ ↦ ⟨h.1, h.2.edge_mem⟩⟩
  left_mem_of_isLink _ _ _ h := h.2.left_mem

/-- `G ↾ F` is the subgraph of `G` restricted to the edges in `F`. Vertices are not changed. -/
scoped infixl:65 " ↾ "  => Graph.edgeRestrict

@[simp]
lemma edgeRestrict_edgeSet (G : Graph α β) (E₀ : Set β) : E(G ↾ E₀) = E₀ ∩ E(G) := rfl

@[simp]
lemma edgeRestrict_vertexSet (G : Graph α β) (E₀ : Set β) : V(G ↾ E₀) = V(G) := rfl

@[simp]
lemma edgeRestrict_le {E₀ : Set β} : G ↾ E₀ ≤ G where
  vertex_subset := rfl.le
  isLink_of_isLink := by
    simp

@[simp]
lemma edgeRestrict_inc_iff : (G ↾ F).Inc e x ↔ G.Inc e x ∧ e ∈ F := by
  simp [Inc, and_comm]

@[simp]
lemma edgeRestrict_isLoopAt_iff : (G ↾ F).IsLoopAt e x ↔ G.IsLoopAt e x ∧ e ∈ F := by
  simp [← isLink_self_iff, and_comm]

@[simp]
lemma edgeRestrict_isNonloopAt_iff : (G ↾ F).IsNonloopAt e x ↔ G.IsNonloopAt e x ∧ e ∈ F := by
  simp_rw [IsNonloopAt]
  aesop

lemma edgeRestrict_mono_right (G : Graph α β) {F₀ F : Set β} (hss : F₀ ⊆ F) : G ↾ F₀ ≤ G ↾ F where
  vertex_subset := rfl.subset
  isLink_of_isLink _ _ _ := fun h ↦ ⟨hss h.1, h.2⟩

lemma edgeRestrict_mono_left (h : H ≤ G) (F : Set β) : H ↾ F ≤ G ↾ F := by
  refine G.le_of_le_le_subset_subset (edgeRestrict_le.trans h) (by simp)
    (by simpa using vertexSet_mono h) ?_
  simp [inter_subset_right.trans (edgeSet_mono h)]

@[simp]
lemma edgeRestrict_inter_edgeSet (G : Graph α β) (F : Set β) : G ↾ (F ∩ E(G)) = G ↾ F :=
  ext_of_le_le (G := G) (by simp) (by simp) (by simp) (by simp)

@[simp]
lemma edgeRestrict_edgeSet_inter (G : Graph α β) (F : Set β) : G ↾ (E(G) ∩ F) = G ↾ F := by
  rw [inter_comm, edgeRestrict_inter_edgeSet]

@[simp]
lemma edgeRestrict_self (G : Graph α β) : G ↾ E(G) = G :=
  ext_of_le_le (G := G) (by simp) (by simp) rfl (by simp)

lemma edgeRestrict_of_superset (G : Graph α β) (hF : E(G) ⊆ F) : G ↾ F = G := by
  rw [← edgeRestrict_inter_edgeSet, inter_eq_self_of_subset_right hF, edgeRestrict_self]

@[simp]
lemma edgeRestrict_edgeRestrict (G : Graph α β) (F₁ F₂ : Set β) : (G ↾ F₁) ↾ F₂ = G ↾ F₁ ∩ F₂ := by
  refine G.ext_of_le_le ?_ (by simp) (by simp) ?_
  · exact edgeRestrict_le.trans (by simp)
  simp only [edgeRestrict_edgeSet]
  rw [← inter_assoc, inter_comm F₂]

@[simp]
lemma le_edgeRestrict_iff : H ≤ (G ↾ F) ↔ H ≤ G ∧ E(H) ⊆ F :=
  ⟨fun h ↦ ⟨h.trans (by simp), (edgeSet_mono h).trans (by simp)⟩,
    fun h ↦ le_of_le_le_subset_subset h.1 (by simp) (by simpa using vertexSet_mono h.1)
    <| subset_inter h.2 (edgeSet_mono h.1)⟩

/-- Delete a set `F` of edges from `G`. This is a special case of `edgeRestrict`,
but we define it with `copy` so that the edge set is definitionally equal to `E(G) \ F`. -/
@[simps!]
def edgeDelete (G : Graph α β) (F : Set β) : Graph α β :=
  (G.edgeRestrict (E(G) \ F)).copy (E := E(G) \ F)
  (IsLink := fun e x y ↦ G.IsLink e x y ∧ e ∉ F) rfl
  (by simp [diff_subset])
  (fun e x y ↦ by
    simp only [edgeRestrict_isLink, mem_diff, and_comm, and_congr_left_iff, and_iff_left_iff_imp]
    exact fun h _ ↦ h.edge_mem)

/-- `G ＼ F` is the subgraph of `G` with the edges in `F` deleted. Vertices are not changed. -/
scoped infixl:65 " ＼ "  => Graph.edgeDelete

lemma edgeDelete_eq_edgeRestrict (G : Graph α β) (F : Set β) :
    G ＼ F = G ↾ (E(G) \ F) := copy_eq_self ..

@[simp]
lemma edgeDelete_inc_iff : (G ＼ F).Inc e x ↔ G.Inc e x ∧ e ∉ F := by
  simp [Inc, and_comm]

@[simp]
lemma edgeDelete_isLoopAt_iff : (G ＼ F).IsLoopAt e x ↔ G.IsLoopAt e x ∧ e ∉ F := by
  simp only [edgeDelete_eq_edgeRestrict, edgeRestrict_isLoopAt_iff, mem_diff, and_congr_right_iff,
    and_iff_right_iff_imp]
  exact fun h _ ↦ h.edge_mem
lemma edgeDelete_isNonloopAt_iff : (G ＼ F).IsNonloopAt e x ↔ G.IsNonloopAt e x ∧ e ∉ F := by
  simp only [edgeDelete_eq_edgeRestrict, edgeRestrict_isNonloopAt_iff, mem_diff,
    and_congr_right_iff, and_iff_right_iff_imp]
  exact fun h _ ↦ h.edge_mem

@[simp]
lemma edgeDelete_le : G ＼ F ≤ G := by
  simp [edgeDelete_eq_edgeRestrict]

@[simp]
lemma edgeDelete_inter_edgeSet : G ＼ (F ∩ E(G)) = G ＼ F := by
  rw [edgeDelete_eq_edgeRestrict, edgeDelete_eq_edgeRestrict, diff_inter_self_eq_diff]

lemma edgeDelete_anti_right (G : Graph α β) {F₀ F : Set β} (hss : F₀ ⊆ F) : G ＼ F ≤ G ＼ F₀ := by
  simp_rw [edgeDelete_eq_edgeRestrict]
  exact G.edgeRestrict_mono_right <| diff_subset_diff_right hss

lemma edgeDelete_mono_left (h : H ≤ G) : H ＼ F ≤ G ＼ F := by
  simp_rw [edgeDelete_eq_edgeRestrict]
  refine (edgeRestrict_mono_left h (E(H) \ F)).trans (G.edgeRestrict_mono_right ?_)
  exact diff_subset_diff_left (edgeSet_mono h)

@[simp]
lemma edgeDelete_edgeDelete (G : Graph α β) (F₁ F₂ : Set β) : G ＼ F₁ ＼ F₂ = G ＼ (F₁ ∪ F₂) := by
  simp only [edgeDelete_eq_edgeRestrict, diff_eq_compl_inter, edgeRestrict_inter_edgeSet,
    edgeRestrict_edgeSet, edgeRestrict_edgeRestrict, compl_union]
  rw [← inter_comm, inter_comm F₁ᶜ, inter_assoc, inter_assoc, inter_self, inter_comm,
    inter_assoc, inter_comm, edgeRestrict_inter_edgeSet]

@[simp]
lemma edgeRestrict_edgeDelete (G : Graph α β) (F₁ F₂ : Set β) : G ↾ F₁ ＼ F₂ = G ↾ (F₁ \ F₂) := by
  rw [edgeDelete_eq_edgeRestrict, edgeRestrict_edgeRestrict, edgeRestrict_edgeSet, diff_eq,
    ← inter_assoc, ← inter_assoc, inter_self, inter_comm F₁, inter_assoc,
    edgeRestrict_edgeSet_inter, diff_eq]

lemma edgeDelete_eq_self (G : Graph α β) (hF : Disjoint E(G) F) : G ＼ F = G := by
  simp [edgeDelete_eq_edgeRestrict, hF.sdiff_eq_left]

@[simp]
lemma le_edgeDelete_iff : H ≤ G ＼ F ↔ H ≤ G ∧ Disjoint E(H) F := by
  simp only [edgeDelete_eq_edgeRestrict, le_edgeRestrict_iff, subset_diff, and_congr_right_iff,
    and_iff_right_iff_imp]
  exact fun hle _ ↦ edgeSet_mono hle

lemma IsNonloopAt.isLoopAt_delete (h : G.IsNonloopAt e x) : (G ＼ {e}).IsLoopAt = G.IsLoopAt := by
  ext f y
  simp only [← isLink_self_iff, edgeDelete_isLink, mem_singleton_iff, and_iff_left_iff_imp]
  rintro h' rfl
  exact h.not_isLoopAt y h'

lemma IsLoopAt.isNonloopAt_delete (h : G.IsLoopAt e x) :
    (G ＼ {e}).IsNonloopAt = G.IsNonloopAt := by
  ext f y
  simp only [isNonloopAt_iff_inc_not_isLoopAt, edgeDelete_inc_iff, mem_singleton_iff, ←
    isLink_self_iff, edgeDelete_isLink, not_and, not_not]
  obtain rfl | hne := eq_or_ne f e
  · simp only [not_true_eq_false, and_false, isLink_self_iff, implies_true, and_true,
      false_iff, not_and, not_not]
    exact fun h' ↦ by rwa [← h.eq_of_inc h']
  simp [hne]

/-- The subgraph of `G` induced by a set `X` of vertices.
The edges are the edges of `G` with both ends in `X`.
(`X` is not required to be a subset of `V(G)` for this definition to work,
even though this is the standard use case) -/
@[simps! vertexSet]
protected def induce (G : Graph α β) (X : Set α) : Graph α β where
  vertexSet := X
  IsLink e x y := G.IsLink e x y ∧ x ∈ X ∧ y ∈ X
  isLink_symm _ _ x := by simp +contextual [G.isLink_comm (x := x)]
  eq_or_eq_of_isLink_of_isLink _ _ _ _ _ h h' := h.1.left_eq_or_eq h'.1
  left_mem_of_isLink := by simp +contextual

/-- `G[X]` is the subgraph of `G` induced by the set `X` of vertices. -/
scoped notation:max G:1000 "[" S "]" => Graph.induce G S

lemma induce_le (hX : X ⊆ V(G)) : G[X] ≤ G :=
  ⟨hX, fun _ _ _ h ↦ h.1⟩

@[simp]
lemma induce_le_iff : G[X] ≤ G ↔ X ⊆ V(G) :=
  ⟨vertexSet_mono, induce_le⟩

@[simp]
lemma induce_isLink_iff {X : Set α} : G[X].IsLink e x y ↔ G.IsLink e x y ∧ x ∈ X ∧ y ∈ X := Iff.rfl

lemma IsLink.induce (h : G.IsLink e x y) (hx : x ∈ X) (hy : y ∈ X) : G[X].IsLink e x y :=
  ⟨h, hx, hy⟩

@[simp]
lemma induce_adj_iff {X : Set α} : G[X].Adj x y ↔ G.Adj x y ∧ x ∈ X ∧ y ∈ X := by simp [Adj]

lemma Adj.induce (h : G.Adj x y) (hx : x ∈ X) (hy : y ∈ X) : G[X].Adj x y :=
  induce_adj_iff.mpr ⟨h, hx, hy⟩

/-- This is too annoying to be a simp lemma. -/
lemma induce_edgeSet (G : Graph α β) (X : Set α) :
    E(G.induce X) = {e | ∃ x y, G.IsLink e x y ∧ x ∈ X ∧ y ∈ X} := rfl

@[simp]
lemma induce_edgeSet_subset (G : Graph α β) (X : Set α) : E(G.induce X) ⊆ E(G) := by
  rintro e ⟨x,y,h, -, -⟩
  exact h.edge_mem

lemma IsLink.mem_induce_iff {X : Set α} (hG : G.IsLink e x y) : e ∈ E(G[X]) ↔ x ∈ X ∧ y ∈ X := by
  simp only [induce_edgeSet, mem_setOf_eq]
  refine ⟨fun ⟨x', y', he, hx', hy'⟩ ↦ ?_, fun h ↦ ⟨x, y, hG, h⟩⟩
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := hG.eq_and_eq_or_eq_and_eq he <;> simp [hx', hy']

lemma induce_induce (G : Graph α β) (X Y : Set α) : G[X][Y] = G[Y] ↾ E(G[X]) := by
  refine Graph.ext rfl fun e x y ↦ ?_
  simp only [induce_isLink_iff, edgeRestrict_isLink]
  obtain he | he := em' (G.IsLink e x y)
  · simp [he]
  rw [he.mem_induce_iff]
  tauto

lemma induce_mono_right (G : Graph α β) (hXY : X ⊆ Y) : G[X] ≤ G[Y] where
  vertex_subset := hXY
  isLink_of_isLink _ _ _ := fun ⟨h, h1, h2⟩ ↦ ⟨h, hXY h1, hXY h2⟩

@[simp]
lemma induce_mono_right_iff (G : Graph α β) : G[X] ≤ G[Y] ↔ X ⊆ Y :=
  ⟨vertexSet_mono, induce_mono_right G⟩

lemma induce_mono_left (h : H ≤ G) (X : Set α) : H[X] ≤ G[X] where
  vertex_subset := le_rfl
  isLink_of_isLink e x y := by
    simp only [induce_isLink_iff, and_imp]
    exact fun hl hx hy => ⟨hl.of_le h, hx, hy⟩

lemma induce_mono (h : H ≤ G) (hXY : X ⊆ Y) : H[X] ≤ G[Y] :=
  (induce_mono_left h X).trans (G.induce_mono_right hXY)

@[simp]
lemma induce_vertexSet_self (G : Graph α β) : G[V(G)] = G := by
  refine G.ext_of_le_le (by simp) (by simp) rfl <| Set.ext fun e ↦
    ⟨fun ⟨_, _, h⟩ ↦ h.1.edge_mem, fun h ↦ ?_⟩
  obtain ⟨x, y, h⟩ := exists_isLink_of_mem_edgeSet h
  exact ⟨x, y, h, h.left_mem, h.right_mem⟩

lemma le_induce_of_le_of_subset (h : H ≤ G) (hV : V(H) ⊆ X) : H ≤ G[X] :=
  ⟨hV, fun _ _ _ h' ↦ ⟨h'.of_le h, hV h'.left_mem, hV h'.right_mem⟩⟩

lemma le_induce_self (h : H ≤ G) : H ≤ G[V(H)] :=
  le_induce_of_le_of_subset h rfl.subset

lemma le_induce_iff (hX : X ⊆ V(G)) : H ≤ G[X] ↔ H ≤ G ∧ V(H) ⊆ X :=
  ⟨fun h ↦ ⟨h.trans (by simpa), vertexSet_mono h⟩, fun h ↦ le_induce_of_le_of_subset h.1 h.2⟩

/-- The graph obtained from `G` by deleting a set of vertices. -/
protected def vertexDelete (G : Graph α β) (X : Set α) : Graph α β := G [V(G) \ X]

/-- `G - X` is the graph obtained from `G` by deleting the set `X` of vertices. -/
scoped notation:max G:1000 " - " S:1000 => Graph.vertexDelete G S

-- instance instHSub : HSub (Graph α β) (Set α) (Graph α β) where
--   hSub := Graph.vertexDelete

lemma vertexDelete_def (G : Graph α β) (X : Set α) : G - X = G [V(G) \ X] := rfl

@[simp]
lemma vertexDelete_vertexSet (G : Graph α β) (X : Set α) : V(G - X) = V(G) \ X := rfl

@[simp]
lemma vertexDelete_isLink_iff (G : Graph α β) (X : Set α) :
    (G - X).IsLink e x y ↔ (G.IsLink e x y ∧ x ∉ X ∧ y ∉ X) := by
  simp only [vertexDelete_def, induce_isLink_iff, mem_diff, and_congr_right_iff]
  exact fun h ↦ by simp [h.left_mem, h.right_mem]

@[simp]
lemma vertexDelete_edgeSet (G : Graph α β) (X : Set α) :
    E(G - X) = {e | ∃ x y, G.IsLink e x y ∧ x ∉ X ∧ y ∉ X} := by
  simp [edgeSet_eq_setOf_exists_isLink]

@[simp]
lemma vertexDelete_empty (G : Graph α β) : G - ∅ = G := by
  simp [vertexDelete_def]

@[simp]
lemma vertexDelete_adj_iff (G : Graph α β) (X : Set α) :
    (G - X).Adj x y ↔ G.Adj x y ∧ x ∉ X ∧ y ∉ X := by
  simp [Adj]

@[simp]
lemma vertexDelete_le : G - X ≤ G :=
  G.induce_le diff_subset

lemma IsLink.mem_vertexDelete_iff {X : Set α} (hG : G.IsLink e x y) :
    e ∈ E(G - X) ↔ x ∉ X ∧ y ∉ X := by
  rw [vertexDelete_def, hG.mem_induce_iff, mem_diff, mem_diff, and_iff_right hG.left_mem,
    and_iff_right hG.right_mem]

lemma vertexDelete_mono_left (h : H ≤ G) : H - X ≤ G - X :=
  induce_mono h <| diff_subset_diff_left <| vertexSet_mono h

lemma vertexDelete_anti_right (hXY : X ⊆ Y) : G - Y ≤ G - X :=
  induce_mono_right _ <| diff_subset_diff_right hXY

@[simp]
lemma edgeRestrict_induce (G : Graph α β) (X : Set α) (F : Set β) : (G ↾ F)[X] = G[X] ↾ F := by
  refine Graph.ext (by simp) fun e x y ↦ ?_
  simp only [induce_isLink_iff, edgeRestrict_isLink]
  tauto

lemma edgeRestrict_vertexDelete (G : Graph α β) (F : Set β) (D : Set α) :
    (G ↾ F) - D = (G - D) ↾ F := by
  refine Graph.ext rfl fun e x y ↦ ?_
  simp only [vertexDelete_isLink_iff, edgeRestrict_isLink]
  tauto

@[simp]
lemma edgeDelete_induce (G : Graph α β) (X : Set α) (F : Set β) : (G ＼ F)[X] = G[X] ＼ F := by
  rw [edgeDelete_eq_edgeRestrict, edgeRestrict_induce, ← edgeRestrict_edgeSet_inter,
    ← inter_diff_assoc, inter_eq_self_of_subset_left (by simp), ← edgeDelete_eq_edgeRestrict]

@[simp]
lemma induce_vertexDelete (G : Graph α β) (X D : Set α) : G[X] - D = G[X \ D] :=
  Graph.ext rfl <| by
  simp only [vertexDelete_isLink_iff, induce_isLink_iff, mem_diff]
  tauto

@[simp]
lemma le_vertexDelete_iff : H ≤ G - X ↔ H ≤ G ∧ Disjoint V(H) X := by
  simp only [vertexDelete_def, le_induce_iff diff_subset, subset_diff, and_congr_right_iff,
    and_iff_right_iff_imp]
  exact fun h _ ↦ vertexSet_mono h

/-! ### Spanning Subgraphs -/

/-- A spanning subgraph of `G` is a subgraph of `G` with the same vertex set. -/
@[mk_iff]
structure IsSpanningSubgraph (H G : Graph α β) : Prop where
  le : H ≤ G
  vertexSet_eq : V(H) = V(G)

/-- `H ≤s G` means that `H` is a spanning subgraph of `G`. -/
infixl:50 " ≤s " => Graph.IsSpanningSubgraph

@[simp]
lemma edgeRestrict_isSpanningSubgraph : G ↾ F ≤s G :=
  ⟨by simp, rfl⟩

@[simp]
lemma edgeDelete_isSpanningSubgraph : G ＼ F ≤s G :=
  ⟨by simp, rfl⟩

lemma IsSpanningSubgraph.of_isSpanningSubgraph_left (h : H ≤s G) (hHK : H ≤ K) (hKG : K ≤ G) :
    H ≤s K where
  le := hHK
  vertexSet_eq := (vertexSet_mono hHK).antisymm ((vertexSet_mono hKG).trans_eq h.vertexSet_eq.symm)

lemma IsSpanningSubgraph.of_isSpanningSubgraph_right (h : H ≤s G) (hHK : H ≤ K) (hKG : K ≤ G) :
    K ≤s G where
  le := hKG
  vertexSet_eq := (vertexSet_mono hKG).antisymm <|
    h.vertexSet_eq.symm.le.trans <| vertexSet_mono hHK

/-! ### Induced Subgraphs -/

/-- An induced subgraph of `G` is a subgraph `H` of `G` such that every link of `G`
involving two vertices of `H` is also a link of `H`. -/
structure IsInducedSubgraph (H G : Graph α β) : Prop where
  le : H ≤ G
  isLink_of_mem_mem : ∀ ⦃e x y⦄, G.IsLink e x y → x ∈ V(H) → y ∈ V(H) → H.IsLink e x y

/-- `H ≤i G` means that `H` is an induced subgraph of `G`. -/
scoped infixl:50 " ≤i " => Graph.IsInducedSubgraph

lemma IsInducedSubgraph.trans {G₁ G₂ G₃ : Graph α β} (h₁₂ : G₁ ≤i G₂) (h₂₃ : G₂ ≤i G₃) :
    G₁ ≤i G₃ :=
  ⟨h₁₂.le.trans h₂₃.le, fun _ _ _ h hx hy ↦ h₁₂.isLink_of_mem_mem
    (h₂₃.isLink_of_mem_mem h (vertexSet_mono h₁₂.le hx) (vertexSet_mono h₁₂.le hy))
    hx hy⟩

lemma isInducedSubgraph_iff :
    H ≤i G ↔ H ≤ G ∧ ∀ ⦃e x y⦄, G.IsLink e x y → x ∈ V(H) → y ∈ V(H) → H.IsLink e x y :=
  ⟨fun h ↦ ⟨h.1, h.2⟩, fun h ↦ ⟨h.1, h.2⟩⟩

lemma induce_isInducedSubgraph (hX : X ⊆ V(G)) : G[X] ≤i G :=
  ⟨by simpa, fun e x y h (hx : x ∈ X) (hy : y ∈ X) ↦ by simp_all⟩

@[simp]
lemma induce_isInducedSubgraph_iff : G[X] ≤i G ↔ X ⊆ V(G) := by
  simp +contextual [isInducedSubgraph_iff]

lemma IsInducedSubgraph.induce_vertexSet_eq (h : H ≤i G) : G[V(H)] = H := by
  have hle : G[V(H)] ≤ G := by simp [vertexSet_mono h.le]
  refine G.ext_of_le_le hle h.le rfl <| Set.ext fun e ↦ ?_
  simp only [induce_edgeSet, mem_setOf_eq]
  refine ⟨fun ⟨x, y, h', hx, hy⟩ ↦ (h.isLink_of_mem_mem h' hx hy).edge_mem, fun h' ↦ ?_⟩
  obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet h'
  exact ⟨x, y, hxy.of_le h.le, hxy.left_mem, hxy.right_mem⟩

/-- An induced subgraph is precisely a subgraph of the form `G[X]` for some `X ⊆ V(G)`.
This version of the lemma can be used with `subst` or `obtain rfl` to replace `H` with `G[X]`. -/
lemma IsInducedSubgraph.exists_eq_induce (h : H ≤i G) : ∃ X ⊆ V(G), H = G[X] :=
  ⟨V(H), vertexSet_mono h.le, h.induce_vertexSet_eq.symm⟩

lemma IsInducedSubgraph.adj_of_adj (h : H ≤i G) (hxy : G.Adj x y) (hx : x ∈ V(H)) (hy : y ∈ V(H)) :
    H.Adj x y := by
  obtain ⟨e, hxy⟩ := hxy
  exact (h.isLink_of_mem_mem hxy hx hy).adj

lemma IsInducedSubgraph.eq_of_isSpanningSubgraph (hi : H ≤i G) (hs : H ≤s G) : H = G := by
  obtain ⟨X, hX, rfl⟩ := hi.exists_eq_induce
  simp [show X = V(G) by simpa using hs.vertexSet_eq]

/-! ### Closed Subgraphs -/

/-- A closed subgraph of `G` is a union of components of `G`. -/
@[mk_iff]
structure IsClosedSubgraph (H G : Graph α β) : Prop where
  le : H ≤ G
  closed : ∀ ⦃e x⦄, G.Inc e x → x ∈ V(H) → e ∈ E(H)

/-- `H ≤c G` means that `H` is a closed subgraph of `G`. i.e. a union of components of `G`. -/
scoped infixl:50 " ≤c " => Graph.IsClosedSubgraph

lemma IsClosedSubgraph.vertexSet_mono (h : H ≤c G) : V(H) ⊆ V(G) := Graph.vertexSet_mono h.le

lemma IsClosedSubgraph.edgeSet_mono (h : H ≤c G) : E(H) ⊆ E(G) := Graph.edgeSet_mono h.le

lemma IsClosedSubgraph.isInducedSubgraph (h : H ≤c G) : H ≤i G where
  le := h.le
  isLink_of_mem_mem _ _ _ he hx _ := he.of_le_of_mem h.le (h.closed he.inc_left hx)

lemma IsClosedSubgraph.trans {G₁ G₂ G₃ : Graph α β} (h₁ : G₁ ≤c G₂) (h₂ : G₂ ≤c G₃) : G₁ ≤c G₃ where
  le := h₁.le.trans h₂.le
  closed _ _ h hx :=  h₁.closed (h.of_le_of_mem h₂.le (h₂.closed h (h₁.vertexSet_mono hx))) hx

@[simp]
lemma isClosedSubgraph_self : G ≤c G where
  le := le_rfl
  closed _ _ he _ := he.edge_mem

lemma Inc.of_isClosedSubgraph_of_mem (h : G.Inc e x) (hle : H ≤c G) (hx : x ∈ V(H)) : H.Inc e x :=
  h.of_le_of_mem hle.le (hle.closed h hx)

lemma IsLink.of_isClosedSubgraph_of_mem (h : G.IsLink e x y) (hle : H ≤c G) (hx : x ∈ V(H)) :
    H.IsLink e x y :=
  h.of_le_of_mem hle.le (h.inc_left.of_isClosedSubgraph_of_mem hle hx).edge_mem

lemma IsClosedSubgraph.isLink_iff_of_mem (h : H ≤c G) (hx : x ∈ V(H)) :
    H.IsLink e x y ↔ G.IsLink e x y :=
  ⟨fun he ↦ he.of_le h.le, fun he ↦ he.of_isClosedSubgraph_of_mem h hx⟩

lemma IsClosedSubgraph.mem_iff_mem_of_isLink (h : H ≤c G) (he : G.IsLink e x y) :
    x ∈ V(H) ↔ y ∈ V(H) := by
  refine ⟨fun hin ↦ ?_, fun hin ↦ ?_⟩
  on_goal 2 => rw [isLink_comm] at he
  all_goals rw [← h.isLink_iff_of_mem hin] at he; exact he.right_mem

lemma IsClosedSubgraph.mem_tfae_of_isLink (h : H ≤c G) (he : G.IsLink e x y) :
    List.TFAE [x ∈ V(H), y ∈ V(H), e ∈ E(H)] := by
  tfae_have 1 → 2 := (h.mem_iff_mem_of_isLink he).mp
  tfae_have 2 → 3 := (he.symm.of_isClosedSubgraph_of_mem h · |>.edge_mem)
  tfae_have 3 → 1 := (he.of_le_of_mem h.le · |>.left_mem)
  tfae_finish

lemma IsClosedSubgraph.adj_of_adj_of_mem (h : H ≤c G) (hx : x ∈ V(H)) (hxy : G.Adj x y) :
    H.Adj x y := by
  obtain ⟨e, hexy⟩ := hxy
  exact (hexy.of_isClosedSubgraph_of_mem h hx).adj

lemma IsClosedSubgraph.mem_iff_mem_of_adj (h : H ≤c G) (hxy : G.Adj x y) :
    x ∈ V(H) ↔ y ∈ V(H) := by
  obtain ⟨e, hexy⟩ := hxy
  exact mem_iff_mem_of_isLink h hexy

lemma IsClosedSubgraph.of_le_of_le {G₁ : Graph α β} (hHG : H ≤c G) (hHG₁ : H ≤ G₁) (hG₁ : G₁ ≤ G):
    H ≤c G₁ where
  le := hHG₁
  closed _ _ he hx := ((he.of_le hG₁).of_isClosedSubgraph_of_mem hHG hx).edge_mem

lemma IsClosedSubgraph.diff {H₁ H₂ : Graph α β} (h₁ : H₁ ≤c G) (h₂ : H₂ ≤c G) :
    H₁ - V(H₂) ≤c G where
  le := vertexDelete_le.trans h₁.le
  closed e x he hx := by
    simp only [vertexDelete_edgeSet, mem_setOf_eq]
    simp only [vertexDelete_vertexSet, mem_diff] at hx
    obtain ⟨y, hexy⟩ := he
    refine ⟨x, y, hexy.of_isClosedSubgraph_of_mem h₁ hx.1, hx.2, fun hy ↦ hx.2 ?_⟩
    refine (hexy.symm.of_isClosedSubgraph_of_mem h₂ hy).right_mem

lemma IsClosedSubgraph.compl (h : H ≤c G) : G - V(H) ≤c G :=
  G.isClosedSubgraph_self.diff h

lemma not_isClosedSubgraph_iff_of_IsInducedSubgraph (hle : H ≤i G) : ¬ H ≤c G ↔ ∃ x y, G.Adj x y ∧
    x ∈ V(H) ∧ y ∉ V(H) := by
  rw [not_iff_comm]
  push_neg
  exact ⟨fun hncl ↦ ⟨hle.le, fun e x ⟨y, hexy⟩ hxH =>
    hle.isLink_of_mem_mem hexy hxH (hncl x y ⟨e, hexy⟩ hxH) |>.edge_mem⟩,
    fun hcl x y hexy hx ↦ (hcl.mem_iff_mem_of_adj hexy).mp hx⟩

lemma IsClosedSubgraph.of_edgeDelete_iff (hclF : H ≤c G ＼ F) : H ≤c G ↔ E(G) ∩ F ⊆ E(G - V(H)) := by
  rw [vertexDelete_edgeSet]
  refine ⟨fun hcl f hf ↦ ?_, fun hF ↦ ⟨hclF.le.trans edgeDelete_le, fun e x he hxH => ?_⟩⟩
  · by_contra! hfH
    simp only [mem_setOf_eq, not_exists, not_and, not_not] at hfH
    refine (hclF.edgeSet_mono ?_).2 hf.2
    obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet hf.1
    obtain hx | hy := or_iff_not_imp_left.mpr <| hfH x y hxy
    · exact hcl.closed ⟨_, hxy⟩ hx
    · exact hcl.closed ⟨_, hxy.symm⟩ hy
  · have heF : e ∉ F := fun heF => by
      obtain ⟨u, v, heuv, hunH, hvnH⟩ := hF ⟨he.edge_mem, heF⟩
      obtain rfl | rfl := he.eq_or_eq_of_isLink heuv <;> exact (‹x ∉ V(H)› hxH).elim
    exact hclF.closed (by simp [he, heF]) hxH

/-! ### Components -/

/-- A component of `G` is a minimal nonempty closed subgraph of `G`. -/
def IsCompOf (H G : Graph α β) : Prop := Minimal (fun H ↦ H ≤c G ∧ V(H).Nonempty) H

lemma IsCompOf.isClosedSubgraph (h : H.IsCompOf G) : H ≤c G :=
  h.prop.1

lemma IsCompOf.isInducedSubgraph (hHco : H.IsCompOf G) : H ≤i G :=
  hHco.isClosedSubgraph.isInducedSubgraph

lemma IsCompOf.le (h : H.IsCompOf G) : H ≤ G :=
  h.isClosedSubgraph.le

lemma IsCompOf.nonempty (h : H.IsCompOf G) : V(H).Nonempty :=
  h.prop.2

end Graph
