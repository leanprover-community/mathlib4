/-
Copyright (c) 2025 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson, Jun Kwon
-/
module

public import Mathlib.Combinatorics.Graph.Basic
public import Mathlib.Tactic.TFAE

/-!
# Subgraphs of multigraphs

This file develops the basic theory of subgraphs for multigraphs `Graph α β`:
the subgraph relation, standard classes of subgraphs (spanning, induced, closed),
and components.

## Main definitions

- `H ≤ G`: the subgraph relation as a partial order on graphs.
- `H ≤s G` (`Graph.IsSpanningSubgraph`): `H` has the same vertex set as `G`.
- `H ≤i G` (`Graph.IsInducedSubgraph`): `H` contains every ambient link between its vertices.
- `H ≤c G` (`Graph.IsClosedSubgraph`): `H` is a union of components of `G`.

## Implementation notes

Following the overall design of `Graph`, subgraphs are terms of the same type `Graph α β`
rather than a separate `Subgraph` structure. This allows us to reuse notation and lemmas
uniformly and to express the subgraph order directly as a partial order on `Graph α β`.

## Tags

graphs, subgraph, induced subgraph, spanning subgraph, closed subgraph, component
-/

@[expose] public section

variable {α β : Type*} {x y z u v w : α} {e f : β} {G G₁ G₂ H H₁ H₂ K : Graph α β} {F F₁ F₂ : Set β}
   {X Y : Set α}

open Set

open scoped Sym2

namespace Graph

/-- `H ≤ G` means `V(H) ⊆ V(G)` and every link of `H` is a link of `G`. The subgraph order is a
partial order on graphs. -/
instance : PartialOrder (Graph α β) where
  le H G := V(H) ⊆ V(G) ∧ ∀ ⦃e x y⦄, H.IsLink e x y → G.IsLink e x y
  le_refl _ := by simp
  le_trans _ _ _ h₁ h₂ := ⟨h₁.1.trans h₂.1, fun _ _ _ h ↦ h₂.2 (h₁.2 h)⟩
  le_antisymm G H h₁ h₂ := Graph.ext (h₁.1.antisymm h₂.1)
    fun e x y ↦ ⟨fun a ↦ h₁.2 a, fun a ↦ h₂.2 a⟩

lemma le_iff : H ≤ G ↔ V(H) ⊆ V(G) ∧ ∀ ⦃e x y⦄, H.IsLink e x y → G.IsLink e x y :=
  ⟨fun h ↦ ⟨h.1, h.2⟩, fun h ↦ ⟨h.1, h.2⟩⟩

@[gcongr]
lemma vertexSet_mono (h : H ≤ G) : V(H) ⊆ V(G) :=
  h.1

@[gcongr]
lemma IsLink.mono (hHG : H ≤ G) (h : H.IsLink e x y) : G.IsLink e x y :=
  hHG.2 h

@[gcongr]
lemma edgeSet_mono (h : H ≤ G) : E(H) ⊆ E(G) := by
  intro e he
  obtain ⟨x, y, h'⟩ := exists_isLink_of_mem_edgeSet he
  exact (h'.mono h).edge_mem

private lemma IsLink.anti_of_mem (h : G.IsLink e x y) (hHG : H ≤ G) (he : e ∈ E(H)) :
    H.IsLink e x y := by
  obtain ⟨u, v, huv⟩ := exists_isLink_of_mem_edgeSet he
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := (huv.mono hHG).eq_and_eq_or_eq_and_eq h
  · assumption
  exact huv.symm

lemma isLink_iff_of_le (hHG : H ≤ G) (he : e ∈ E(H)) : H.IsLink e x y ↔ G.IsLink e x y :=
  ⟨fun h ↦ h.mono hHG, fun h ↦ h.anti_of_mem hHG he⟩

lemma isLink_eqOn_of_le (hHG : H ≤ G) : EqOn H.IsLink G.IsLink E(H) := by
  rintro e he
  ext x y
  exact isLink_iff_of_le hHG he

/-- Two subgraphs of the same graph are compatible. -/
lemma Compatible.of_le_le (hH₁G : H₁ ≤ G) (hH₂G : H₂ ≤ G) : H₁.Compatible H₂ :=
  fun _ he₁ he₂ _ _ ↦ isLink_iff_of_le hH₁G he₁ |>.trans <| (isLink_iff_of_le hH₂G he₂).symm

lemma Compatible.of_le (hHG : H ≤ G) : H.Compatible G := Compatible.of_le_le hHG le_rfl

lemma Compatible.of_ge (hHG : G ≤ H) : H.Compatible G := Compatible.of_le_le hHG le_rfl |>.symm

lemma Compatible.anti_left (hG₁G : G₁ ≤ G) (h : Compatible G H) : Compatible G₁ H :=
  fun _ he₁ he₂ _ _ ↦ isLink_iff_of_le hG₁G he₁ |>.trans <| h (edgeSet_mono hG₁G he₁) he₂ ..

lemma Compatible.anti_right (hH₁H : H₁ ≤ H) (h : Compatible G H) : Compatible G H₁ :=
  (h.symm.anti_left hH₁H).symm

lemma Compatible.anti (hG₁G : G₁ ≤ G) (hH₁H : H₁ ≤ H) (h : G.Compatible H) : G₁.Compatible H₁ :=
  (h.anti_left hG₁G).anti_right hH₁H

@[gcongr]
lemma Inc.mono (hHG : H ≤ G) (h : H.Inc e x) : G.Inc e x :=
  (h.choose_spec.mono hHG).inc_left

lemma inc_iff_of_le (hHG : H ≤ G) (he : e ∈ E(H)) : H.Inc e x ↔ G.Inc e x := by
  simp_rw [Graph.Inc, isLink_iff_of_le hHG he]

lemma inc_eqOn_of_le (hHG : H ≤ G) : EqOn H.Inc G.Inc E(H) := by
  rintro e he
  ext x
  exact inc_iff_of_le hHG he

lemma IsLoopAt.mono (hHG : H ≤ G) (h : H.IsLoopAt e x) : G.IsLoopAt e x :=
  IsLink.mono hHG h

lemma isLoopAt_iff_of_le (hHG : H ≤ G) (he : e ∈ E(H)) : H.IsLoopAt e x ↔ G.IsLoopAt e x := by
  unfold Graph.IsLoopAt
  rw [isLink_iff_of_le hHG he]

lemma isLoopAt_eqOn_of_le (hHG : H ≤ G) : EqOn H.IsLoopAt G.IsLoopAt E(H) := by
  rintro e he
  ext x
  exact isLoopAt_iff_of_le hHG he

lemma IsNonloopAt.mono (hHG : H ≤ G) (h : H.IsNonloopAt e x) : G.IsNonloopAt e x := by
  obtain ⟨y, hxy, he⟩ := h
  exact ⟨y, hxy, he.mono hHG⟩

lemma isNonloopAt_iff_of_le (hHG : H ≤ G) (he : e ∈ E(H)) :
    H.IsNonloopAt e x ↔ G.IsNonloopAt e x := by
  simp_rw [Graph.IsNonloopAt, isLink_iff_of_le hHG he]

lemma isNonloopAt_eqOn_of_le (hHG : H ≤ G) : EqOn H.IsNonloopAt G.IsNonloopAt E(H) := by
  rintro e he
  ext x
  exact isNonloopAt_iff_of_le hHG he

@[gcongr]
lemma Adj.mono (hHG : H ≤ G) (h : H.Adj x y) : G.Adj x y :=
  (h.choose_spec.mono hHG).adj

lemma le_iff_compatible_subset_subset : G ≤ H ↔ Compatible G H ∧ V(G) ⊆ V(H) ∧ E(G) ⊆ E(H) :=
  ⟨fun h ↦ ⟨Compatible.of_le h, h.1, edgeSet_mono h⟩, fun ⟨h, hV, hE⟩ ↦
    ⟨hV, fun _ _ _ hxy ↦ h hxy.edge_mem (hE hxy.edge_mem) .. |>.mp hxy⟩⟩

lemma Compatible.le_iff (hH : Compatible H₁ H₂) : H₁ ≤ H₂ ↔ V(H₁) ⊆ V(H₂) ∧ E(H₁) ⊆ E(H₂) :=
  le_iff_compatible_subset_subset.trans (by tauto)

lemma Compatible.ext (hV : V(H₁) = V(H₂)) (hE : E(H₁) = E(H₂)) (h : Compatible H₁ H₂) : H₁ = H₂ :=
  (h.le_iff.mpr ⟨hV.subset, hE.subset⟩).antisymm <| h.symm.le_iff.mpr ⟨hV.superset, hE.superset⟩

lemma vertexSet_ssubset_or_edgeSet_ssubset_of_lt (hGH : G < H) : V(G) ⊂ V(H) ∨ E(G) ⊂ E(H) := by
  rw [lt_iff_le_and_ne] at hGH
  simp only [ssubset_iff_subset_ne, vertexSet_mono hGH.1, ne_eq, true_and, edgeSet_mono hGH.1]
  by_contra! heq
  exact hGH.2 <| (Compatible.of_le_le hGH.1 le_rfl).ext heq.1 heq.2

/-! ### Spanning Subgraphs -/

/-- `H ≤s G` (`Graph.IsSpanningSubgraph`) is a subgraph of `G` with the same vertex set. -/
@[mk_iff]
structure IsSpanningSubgraph (H G : Graph α β) : Prop where
  le : H ≤ G
  vertexSet_eq : V(H) = V(G)

@[inherit_doc IsSpanningSubgraph]
infixl:50 " ≤s " => Graph.IsSpanningSubgraph

lemma IsSpanningSubgraph.trans (h₁ : G ≤s G₁) (h₁₂ : G₁ ≤s G₂) : G ≤s G₂ :=
  ⟨h₁.le.trans h₁₂.le, h₁.vertexSet_eq.trans h₁₂.vertexSet_eq⟩

instance : IsPartialOrder (Graph α β) (· ≤s ·) where
  refl _ := ⟨le_rfl, rfl⟩
  trans _ _ _ h₁ h₂ := h₁.trans h₂
  antisymm _ _ h₁ h₂ := antisymm h₁.le h₂.le

lemma IsSpanningSubgraph.mono_right (hHK : H ≤ K) (hKG : K ≤ G) (h : H ≤s G) : H ≤s K where
  le := hHK
  vertexSet_eq := (vertexSet_mono hHK).antisymm ((vertexSet_mono hKG).trans_eq h.vertexSet_eq.symm)

lemma IsSpanningSubgraph.mono_left (hHK : H ≤ K) (hKG : K ≤ G) (h : H ≤s G) : K ≤s G where
  le := hKG
  vertexSet_eq := (vertexSet_mono hKG).antisymm <|
    h.vertexSet_eq.symm.le.trans <| vertexSet_mono hHK

/-! ### Induced Subgraphs -/

/-- `H ≤i G` (`Graph.IsInducedSubgraph`) is a subgraph of `G` such that every link of `G`
involving two vertices of `H` is also a link of `H`. -/
@[mk_iff]
structure IsInducedSubgraph (H G : Graph α β) : Prop where
  le : H ≤ G
  isLink_of_mem_mem : ∀ ⦃e x y⦄, G.IsLink e x y → x ∈ V(H) → y ∈ V(H) → H.IsLink e x y

@[inherit_doc IsInducedSubgraph]
scoped infixl:50 " ≤i " => Graph.IsInducedSubgraph

lemma IsInducedSubgraph.trans (h₁ : G ≤i G₁) (h₂ : G₁ ≤i G₂) : G ≤i G₂ :=
  ⟨h₁.le.trans h₂.le, fun _ _ _ h hx hy ↦ h₁.isLink_of_mem_mem
    (h₂.isLink_of_mem_mem h (vertexSet_mono h₁.le hx) (vertexSet_mono h₁.le hy)) hx hy⟩

instance : IsPartialOrder (Graph α β) (· ≤i ·) where
  refl _ := ⟨le_rfl, by tauto⟩
  trans _ _ _ h₁ h₂ := h₁.trans h₂
  antisymm _ _ h₁ h₂ := antisymm h₁.le h₂.le

lemma IsInducedSubgraph.adj_iff_adj (hx : x ∈ V(H)) (hy : y ∈ V(H)) (h : H ≤i G) :
    H.Adj x y ↔ G.Adj x y := by
  refine ⟨(·.mono h.le), fun hxy ↦ ?_⟩
  obtain ⟨e, hxy⟩ := hxy
  exact (h.isLink_of_mem_mem hxy hx hy).adj

/-! ### Closed Subgraphs -/

/-- `H ≤c G` (`Graph.IsClosedSubgraph`) is a union of components of `G`. -/
@[mk_iff]
structure IsClosedSubgraph (H G : Graph α β) : Prop where
  le : H ≤ G
  closed : ∀ ⦃e x⦄, G.Inc e x → x ∈ V(H) → e ∈ E(H)

@[inherit_doc IsClosedSubgraph]
scoped infixl:50 " ≤c " => Graph.IsClosedSubgraph

namespace IsClosedSubgraph

lemma vertexSet_mono (h : H ≤c G) : V(H) ⊆ V(G) := Graph.vertexSet_mono h.le

lemma edgeSet_mono (h : H ≤c G) : E(H) ⊆ E(G) := Graph.edgeSet_mono h.le

lemma isInducedSubgraph (h : H ≤c G) : H ≤i G where
  le := h.le
  isLink_of_mem_mem _ _ _ he hx _ := he.anti_of_mem h.le (h.closed he.inc_left hx)

lemma trans (h₁ : G ≤c G₁) (h₂ : G₁ ≤c G₂) : G ≤c G₂ where
  le := h₁.le.trans h₂.le
  closed _ _ h hx :=  h₁.closed (h.of_compatible (Compatible.of_ge h₂.le)
    (h₂.closed h (h₁.vertexSet_mono hx))) hx

instance : IsPartialOrder (Graph α β) (· ≤c ·) where
  refl _ := ⟨le_rfl, fun _ _ h _ ↦ h.edge_mem⟩
  trans _ _ _ h₁ h₂ := h₁.trans h₂
  antisymm _ _ h₁ h₂ := antisymm h₁.le h₂.le

@[simp]
lemma rfl : G ≤c G where
  le := le_rfl
  closed _ _ he _ := he.edge_mem

lemma inc_iff_of_mem (hx : x ∈ V(H)) (hHG : H ≤c G) : H.Inc e x ↔ G.Inc e x :=
  ⟨(·.mono hHG.le), fun he ↦ he.of_compatible (Compatible.of_ge hHG.le) (hHG.closed he hx)⟩

lemma isLink_iff_of_mem (hx : x ∈ V(H)) (hHG : H ≤c G) : H.IsLink e x y ↔ G.IsLink e x y :=
  ⟨(·.mono hHG.le), fun h ↦ h.anti_of_mem hHG.le ((hHG.inc_iff_of_mem hx).mpr h.inc_left).edge_mem⟩

lemma mem_iff_of_isLink (he : G.IsLink e x y) (hHG : H ≤c G) : x ∈ V(H) ↔ y ∈ V(H) := by
  refine ⟨fun hin ↦ ?_, fun hin ↦ ?_⟩
  on_goal 2 => rw [isLink_comm] at he
  all_goals rw [← hHG.isLink_iff_of_mem hin] at he; exact he.right_mem

lemma mem_tfae_of_isLink (he : G.IsLink e x y) (hHG : H ≤c G) :
    List.TFAE [x ∈ V(H), y ∈ V(H), e ∈ E(H)] := by
  tfae_have 1 → 2 := (hHG.mem_iff_of_isLink he).mp
  tfae_have 2 → 3 := (hHG.isLink_iff_of_mem · |>.mpr he.symm |>.edge_mem)
  tfae_have 3 → 1 := (he.anti_of_mem hHG.le · |>.left_mem)
  tfae_finish

lemma adj_iff_of_mem (hx : x ∈ V(H)) (hHG : H ≤c G) : H.Adj x y ↔ G.Adj x y :=
  ⟨(·.mono hHG.le), fun ⟨_, hxy⟩ ↦ (hHG.isLink_iff_of_mem hx |>.mpr hxy).adj⟩

lemma mem_iff_of_adj (hxy : G.Adj x y) (hHG : H ≤c G) : x ∈ V(H) ↔ y ∈ V(H) := by
  obtain ⟨e, hexy⟩ := hxy
  exact hHG.mem_iff_of_isLink hexy

lemma anti_right (hHG₁ : H ≤ G₁) (hG₁ : G₁ ≤ G) (hHG : H ≤c G) : H ≤c G₁ where
  le := hHG₁
  closed _ _ he hx := hHG.inc_iff_of_mem hx |>.mpr (he.mono hG₁) |>.edge_mem

lemma not_iff_of_IsInducedSubgraph (hHG : H ≤i G) :
    ¬ H ≤c G ↔ ∃ x y, G.Adj x y ∧ x ∈ V(H) ∧ y ∉ V(H) := by
  rw [not_iff_comm]
  push_neg
  exact ⟨fun hncl ↦ ⟨hHG.le, fun e x ⟨y, hexy⟩ hxH =>
    hHG.isLink_of_mem_mem hexy hxH (hncl x y ⟨e, hexy⟩ hxH) |>.edge_mem⟩,
    fun hcl _ _ hexy ↦ (hcl.mem_iff_of_adj hexy).mp⟩

end Graph.IsClosedSubgraph
