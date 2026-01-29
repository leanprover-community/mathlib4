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

- `Graph.copy`: produce a graph equal to a given one but with definitional conveniences.
- `Graph.IsSubgraph`: the subgraph relation; used as the partial order `≤` on graphs.
- `Graph.IsSpanningSubgraph` (notation `≤s`): same vertex set as the ambient graph.
- `Graph.IsInducedSubgraph` (notation `≤i`): contains every ambient link between its vertices.
- `Graph.IsClosedSubgraph` (notation `≤c`): union of components of the ambient graph.
- `Graph.IsCompOf`: components, defined as minimal nonempty closed subgraphs.

## Notation

- `H ≤ G` means `H` is a subgraph of `G` (`Graph.IsSubgraph`).
- `H ≤s G` means `H` is a spanning subgraph of `G`.
- `H ≤i G` means `H` is an induced subgraph of `G`.
- `H ≤c G` means `H` is a closed subgraph of `G` (a union of components of `G`).

## Implementation notes

Following the overall design of `Graph`, subgraphs are terms of the same type `Graph α β`
rather than a separate `Subgraph` structure. This allows us to reuse notation and lemmas
uniformly and to express the subgraph order directly as a partial order on `Graph α β`.

## Tags

graphs, subgraph, induced subgraph, spanning subgraph, closed subgraph, component
-/

@[expose] public section

variable {α β : Type*} {x y z u v w : α} {e f : β} {G H K : Graph α β} {F F₁ F₂ : Set β}
    {X Y : Set α}

initialize_simps_projections Graph (IsLink → isLink)

open Set

open scoped Sym2

namespace Graph

/-- `Graph.copy` produces a graph equal to `G` but with provided definitional choices
for `vertexSet`, `edgeSet`, and `IsLink`. This is mainly useful for improving
definitional equalities while keeping the same underlying graph. -/
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

/-- `H ≤ G` means `V(H) ⊆ V(G)` and every link of `H` is a link of `G`. The subgraph order is a
partial order on graphs. -/
instance : PartialOrder (Graph α β) where
  le H G := V(H) ⊆ V(G) ∧ ∀ ⦃e x y⦄, H.IsLink e x y → G.IsLink e x y
  le_refl _ := ⟨rfl.subset, by simp⟩
  le_trans _ _ _ h₁ h₂ := ⟨h₁.1.trans h₂.1, fun _ _ _ h ↦ h₂.2 (h₁.2 h)⟩
  le_antisymm G H h₁ h₂ := Graph.ext (h₁.1.antisymm h₂.1)
    fun e x y ↦ ⟨fun a ↦ h₁.2 a, fun a ↦ h₂.2 a⟩

@[gcongr]
lemma IsLink.mono (hle : H ≤ G) (h : H.IsLink e x y) : G.IsLink e x y :=
  hle.2 h

lemma IsLink.of_le_of_mem (h : G.IsLink e x y) (hle : H ≤ G) (he : e ∈ E(H)) : H.IsLink e x y := by
  obtain ⟨u, v, huv⟩ := exists_isLink_of_mem_edgeSet he
  obtain ⟨rfl, rfl⟩ | ⟨rfl,rfl⟩ := (huv.mono hle).eq_and_eq_or_eq_and_eq h
  · assumption
  exact huv.symm

@[gcongr]
lemma Inc.mono (hle : H ≤ G) (h : H.Inc e x) : G.Inc e x :=
  (h.choose_spec.mono hle).inc_left

lemma Inc.of_le_of_mem (h : G.Inc e x) (hle : H ≤ G) (he : e ∈ E(H)) : H.Inc e x := by
  obtain ⟨y, hy⟩ := h
  exact (hy.of_le_of_mem hle he).inc_left

lemma IsLoopAt.mono (h : H.IsLoopAt e x) (hle : H ≤ G) : G.IsLoopAt e x :=
  IsLink.mono hle h

lemma IsNonloopAt.mono (h : H.IsNonloopAt e x) (hle : H ≤ G) : G.IsNonloopAt e x := by
  obtain ⟨y, hxy, he⟩ := h
  exact ⟨y, hxy, he.mono hle⟩

lemma Adj.mono (h : H.Adj x y) (hle : H ≤ G) : G.Adj x y :=
  (h.choose_spec.mono hle).adj

@[gcongr]
lemma vertexSet_mono (h : H ≤ G) : V(H) ⊆ V(G) :=
  h.1

@[gcongr]
lemma edgeSet_mono (h : H ≤ G) : E(H) ⊆ E(G) := by
  refine fun e he ↦ ?_
  obtain ⟨x, y, h'⟩ := exists_isLink_of_mem_edgeSet he
  exact (h'.mono h).edge_mem

lemma le_iff : H ≤ G ↔ V(H) ⊆ V(G) ∧ ∀ ⦃e x y⦄, H.IsLink e x y → G.IsLink e x y :=
  ⟨fun h ↦ ⟨h.1, h.2⟩, fun h ↦ ⟨h.1, h.2⟩⟩

lemma isLink_iff_isLink_of_le_of_mem (hle : H ≤ G) (he : e ∈ E(H)) :
    G.IsLink e x y ↔ H.IsLink e x y :=
  ⟨fun h ↦ h.of_le_of_mem hle he, fun h ↦ h.mono hle⟩

lemma le_of_le_le_subset_subset {H₁ H₂ : Graph α β} (h₁ : H₁ ≤ G) (h₂ : H₂ ≤ G) (hV : V(H₁) ⊆ V(H₂))
    (hE : E(H₁) ⊆ E(H₂)) : H₁ ≤ H₂ := by
  refine ⟨hV, fun e x y h ↦ ?_⟩
  rw [← G.isLink_iff_isLink_of_le_of_mem h₂ (hE h.edge_mem)]
  exact h.mono h₁

lemma ext_of_le_le {H₁ H₂ : Graph α β} (h₁ : H₁ ≤ G) (h₂ : H₂ ≤ G) (hV : V(H₁) = V(H₂))
    (hE : E(H₁) = E(H₂)) : H₁ = H₂ :=
  (le_of_le_le_subset_subset h₁ h₂ hV.subset hE.subset).antisymm <|
    (le_of_le_le_subset_subset h₂ h₁ hV.symm.subset hE.symm.subset)

lemma isLink_iff_of_le (hle : H ≤ G) (he : e ∈ E(H)) : H.IsLink e x y ↔ G.IsLink e x y :=
  ⟨fun h ↦ h.mono hle, fun h ↦ h.of_le_of_mem hle he⟩

lemma isLink_eqOn_of_le (hle : H ≤ G) : EqOn H.IsLink G.IsLink E(H) := by
  rintro e he
  ext x y
  exact isLink_iff_of_le hle he

lemma inc_iff_of_le (hle : H ≤ G) (he : e ∈ E(H)) : H.Inc e x ↔ G.Inc e x := by
  simp_rw [Graph.Inc, isLink_iff_of_le hle he]

lemma inc_eqOn_of_le (hle : H ≤ G) : EqOn H.Inc G.Inc E(H) := by
  rintro e he
  ext x
  exact inc_iff_of_le hle he

lemma isLoopAt_iff_of_le (hle : H ≤ G) (he : e ∈ E(H)) : H.IsLoopAt e x ↔ G.IsLoopAt e x := by
  unfold Graph.IsLoopAt
  rw [isLink_iff_of_le hle he]

lemma isLoopAt_eqOn_of_le (hle : H ≤ G) : EqOn H.IsLoopAt G.IsLoopAt E(H) := by
  rintro e he
  ext x
  exact isLoopAt_iff_of_le hle he

lemma isNonloopAt_iff_of_le (hle : H ≤ G) (he : e ∈ E(H)) :
    H.IsNonloopAt e x ↔ G.IsNonloopAt e x := by
  simp_rw [Graph.IsNonloopAt, isLink_iff_of_le hle he]

lemma isNonloopAt_eqOn_of_le (hle : H ≤ G) : EqOn H.IsNonloopAt G.IsNonloopAt E(H) := by
  rintro e he
  ext x
  exact isNonloopAt_iff_of_le hle he

lemma vertexSet_ssubset_or_edgeSet_ssubset_of_lt (h : G < H) : V(G) ⊂ V(H) ∨ E(G) ⊂ E(H) := by
  rw [lt_iff_le_and_ne] at h
  simp only [ssubset_iff_subset_ne, vertexSet_mono h.1, ne_eq, true_and, edgeSet_mono h.1]
  by_contra! heq
  exact h.2 <| ext_of_le_le h.1 le_rfl heq.1 heq.2

/-! ### Spanning Subgraphs -/

/-- A spanning subgraph of `G` is a subgraph of `G` with the same vertex set. -/
@[mk_iff]
structure IsSpanningSubgraph (H G : Graph α β) : Prop where
  le : H ≤ G
  vertexSet_eq : V(H) = V(G)

/-- `H ≤s G` means that `H` is a spanning subgraph of `G`. -/
infixl:50 " ≤s " => Graph.IsSpanningSubgraph

lemma IsSpanningSubgraph.trans {G₁ G₂ G₃ : Graph α β} (h₁₂ : G₁ ≤s G₂) (h₂₃ : G₂ ≤s G₃) :
    G₁ ≤s G₃ :=
  ⟨h₁₂.le.trans h₂₃.le, h₁₂.vertexSet_eq.trans h₂₃.vertexSet_eq⟩

instance : IsPartialOrder (Graph α β) (· ≤s ·) where
  refl _ := ⟨le_rfl, rfl⟩
  trans _ _ _ h₁ h₂ := h₁.trans h₂
  antisymm _ _ h₁ h₂ := antisymm h₁.le h₂.le

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

instance : IsPartialOrder (Graph α β) (· ≤i ·) where
  refl _ := ⟨le_rfl, by tauto⟩
  trans _ _ _ h₁ h₂ := h₁.trans h₂
  antisymm _ _ h₁ h₂ := antisymm h₁.le h₂.le

lemma isInducedSubgraph_iff :
    H ≤i G ↔ H ≤ G ∧ ∀ ⦃e x y⦄, G.IsLink e x y → x ∈ V(H) → y ∈ V(H) → H.IsLink e x y :=
  ⟨fun h ↦ ⟨h.1, h.2⟩, fun h ↦ ⟨h.1, h.2⟩⟩

lemma IsInducedSubgraph.adj_of_adj (h : H ≤i G) (hxy : G.Adj x y) (hx : x ∈ V(H)) (hy : y ∈ V(H)) :
    H.Adj x y := by
  obtain ⟨e, hxy⟩ := hxy
  exact (h.isLink_of_mem_mem hxy hx hy).adj

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

instance : IsPartialOrder (Graph α β) (· ≤c ·) where
  refl _ := ⟨le_rfl, fun _ _ h _ ↦ h.edge_mem⟩
  trans _ _ _ h₁ h₂ := h₁.trans h₂
  antisymm _ _ h₁ h₂ := antisymm h₁.le h₂.le

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
  ⟨fun he ↦ he.mono h.le, fun he ↦ he.of_isClosedSubgraph_of_mem h hx⟩

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

lemma IsClosedSubgraph.of_le_of_le {G₁ : Graph α β} (hHG : H ≤c G) (hHG₁ : H ≤ G₁) (hG₁ : G₁ ≤ G) :
    H ≤c G₁ where
  le := hHG₁
  closed _ _ he hx := ((he.mono hG₁).of_isClosedSubgraph_of_mem hHG hx).edge_mem

lemma not_isClosedSubgraph_iff_of_IsInducedSubgraph (hle : H ≤i G) : ¬ H ≤c G ↔ ∃ x y, G.Adj x y ∧
    x ∈ V(H) ∧ y ∉ V(H) := by
  rw [not_iff_comm]
  push_neg
  exact ⟨fun hncl ↦ ⟨hle.le, fun e x ⟨y, hexy⟩ hxH =>
    hle.isLink_of_mem_mem hexy hxH (hncl x y ⟨e, hexy⟩ hxH) |>.edge_mem⟩,
    fun hcl x y hexy hx ↦ (hcl.mem_iff_mem_of_adj hexy).mp hx⟩

end Graph
