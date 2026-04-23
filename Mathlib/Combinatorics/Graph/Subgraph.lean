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
and the bottom element `⊥`.

## Main definitions

- `H ≤ G`: the subgraph relation as a partial order on graphs. This is the preferred spelling over
  `H.IsSubgraph G` which it is definitionally equal to.
- `H ≤s G` (`Graph.IsSpanningSubgraph`): `H` has the same vertex set as `G`.
- `H ≤i G` (`Graph.IsInducedSubgraph`): `H` contains every ambient link between its vertices.
- `H ≤c G` (`Graph.IsClosedSubgraph`): `H` is a union of components of `G`.
- `⊥`: empty graph with no vertices or edges as its bottom element.

## Implementation notes

Following the overall design of `Graph`, subgraphs are terms of the same type `Graph α β`
rather than a separate `Subgraph` structure. This allows us to reuse notation and lemmas
uniformly and to express the subgraph order directly as a partial order on `Graph α β`.

`G ≤ H` is the canonical spelling for "G is a subgraph of H". This is definitionally equal to
`G.IsSubgraph H` which exists only for implementation reasons.
The explicit `IsSubgraph` structure is defined so that stronger subgraph notions
(such as `IsSpanningSubgraph`, `IsInducedSubgraph`, and `IsClosedSubgraph`) can extend it.
This allows them to inherit fundamental fields and lemmas like `vertexSet_mono` and `edgeSet_mono`
without lemma duplication. However, in statements and proofs, users use `G ≤ H` instead.
The relation `≤` is the `simp` normal form, and the API is developed entirely in terms of it.

## Tags

graphs, subgraph, induced subgraph, spanning subgraph, closed subgraph
-/

@[expose] public section

variable {α β : Type*} {x y z u v w : α} {e f : β} {G G₁ G₂ H H₁ H₂ K : Graph α β} {F F₁ F₂ : Set β}
   {X Y : Set α}

open Set

open scoped Sym2

namespace Graph

section Subgraph

/-- `IsSubgraph H G` is NOT the preferred spelling for the subgraph relation. Please use
`H ≤ G` instead. -/
@[mk_iff]
structure IsSubgraph (H G : Graph α β) : Prop where
  vertexSet_mono : V(H) ⊆ V(G) := by aesop
  isLink_mono : ∀ ⦃e x y⦄, H.IsLink e x y → G.IsLink e x y := by aesop

attribute [gcongr, grind →] IsSubgraph.vertexSet_mono

lemma IsSubgraph.trans (h₁ : H.IsSubgraph G) (h₂ : G.IsSubgraph G₁) : H.IsSubgraph G₁ :=
  ⟨h₁.1.trans h₂.1, fun _ _ _ h ↦ h₂.2 (h₁.2 h)⟩

lemma IsSubgraph.antisymm (h₁ : H.IsSubgraph G) (h₂ : G.IsSubgraph H) : H = G :=
  Graph.ext (h₁.1.antisymm h₂.1) fun _ _ _ ↦ ⟨(h₁.2 ·), (h₂.2 ·)⟩

/-- `H ≤ G` means `H` is a subgraph of `G`. It is defined as `V(H) ⊆ V(G)` and every link of `H`
being a link of `G`. -/
instance : PartialOrder (Graph α β) where
  le := IsSubgraph
  le_refl _ := ⟨le_rfl, fun _ _ _ h ↦ h⟩
  le_trans _ _ _ h₁ h₂ := h₁.trans h₂
  le_antisymm G H h₁ h₂ := h₁.antisymm h₂

@[simp]
lemma isSubgraph_iff_le : H.IsSubgraph G ↔ H ≤ G := .rfl

@[gcongr]
lemma IsLink.mono (hHG : H ≤ G) (h : H.IsLink e x y) : G.IsLink e x y := hHG.2 h

@[gcongr, grind →]
lemma IsSubgraph.edgeSet_mono (h : H ≤ G) : E(H) ⊆ E(G) := by
  intro e he
  obtain ⟨x, y, h'⟩ := exists_isLink_of_mem_edgeSet he
  exact (h'.mono h).edge_mem

private lemma IsLink.anti_of_mem (h : G.IsLink e x y) (hHG : H ≤ G) (he : e ∈ E(H)) :
    H.IsLink e x y := by
  obtain ⟨u, v, huv⟩ := exists_isLink_of_mem_edgeSet he
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := (huv.mono hHG).eq_and_eq_or_eq_and_eq h
  · assumption
  exact huv.symm

lemma IsSubgraph.isLink_iff (hHG : H ≤ G) (he : e ∈ E(H)) : H.IsLink e x y ↔ G.IsLink e x y :=
  ⟨fun h ↦ h.mono hHG, fun h ↦ h.anti_of_mem hHG he⟩

lemma IsSubgraph.isLink_eqOn (hHG : H ≤ G) : EqOn H.IsLink G.IsLink E(H) := by
  rintro e he
  ext x y
  exact isLink_iff hHG he

/-- Two subgraphs of the same graph are compatible. -/
lemma Compatible.of_le_le (hH₁G : H₁ ≤ G) (hH₂G : H₂ ≤ G) : H₁.Compatible H₂ :=
  fun _ he₁ he₂ _ _ ↦ hH₁G.isLink_iff he₁ |>.trans <| (hH₂G.isLink_iff he₂).symm

lemma Compatible.of_le (hHG : H ≤ G) : H.Compatible G := .of_le_le hHG le_rfl
lemma Compatible.of_ge (hHG : G ≤ H) : H.Compatible G := .of_le_le le_rfl hHG

alias IsSubgraph.compatible := Compatible.of_le
alias IsSubgraph.compatible' := Compatible.of_ge

lemma Compatible.anti_left (hG₁G : G₁ ≤ G) (h : Compatible G H) : Compatible G₁ H :=
  fun _ he₁ he₂ _ _ ↦ hG₁G.isLink_iff he₁ |>.trans <| h (hG₁G.edgeSet_mono he₁) he₂ ..

lemma Compatible.anti_right (hH₁H : H₁ ≤ H) (h : Compatible G H) : Compatible G H₁ :=
  (h.symm.anti_left hH₁H).symm

lemma Compatible.anti (hG₁G : G₁ ≤ G) (hH₁H : H₁ ≤ H) (h : G.Compatible H) : G₁.Compatible H₁ :=
  (h.anti_left hG₁G).anti_right hH₁H

@[gcongr]
lemma Inc.mono (hHG : H ≤ G) (h : H.Inc e x) : G.Inc e x :=
  (h.choose_spec.mono hHG).inc_left

lemma IsSubgraph.inc_congr (hHG : H ≤ G) (he : e ∈ E(H)) : H.Inc e x ↔ G.Inc e x := by
  simp_rw [Graph.Inc, hHG.isLink_iff he]

lemma IsSubgraph.inc_eqOn (hHG : H ≤ G) : EqOn H.Inc G.Inc E(H) := by
  rintro e he
  ext x
  exact hHG.inc_congr he

lemma IsLoopAt.mono (hHG : H ≤ G) (h : H.IsLoopAt e x) : G.IsLoopAt e x :=
  IsLink.mono hHG h

lemma IsSubgraph.isLoopAt_congr (hHG : H ≤ G) (he : e ∈ E(H)) :
    H.IsLoopAt e x ↔ G.IsLoopAt e x := by
  unfold Graph.IsLoopAt
  rw [hHG.isLink_iff he]

lemma IsSubgraph.isLoopAt_eqOn (hHG : H ≤ G) : EqOn H.IsLoopAt G.IsLoopAt E(H) := by
  rintro e he
  ext x
  exact hHG.isLoopAt_congr he

lemma IsNonloopAt.mono (hHG : H ≤ G) (h : H.IsNonloopAt e x) : G.IsNonloopAt e x := by
  obtain ⟨y, hxy, he⟩ := h
  exact ⟨y, hxy, he.mono hHG⟩

lemma IsSubgraph.isNonloopAt_congr (hHG : H ≤ G) (he : e ∈ E(H)) :
    H.IsNonloopAt e x ↔ G.IsNonloopAt e x := by
  simp_rw [Graph.IsNonloopAt, hHG.isLink_iff he]

lemma IsSubgraph.isNonloopAt_eqOn (hHG : H ≤ G) : EqOn H.IsNonloopAt G.IsNonloopAt E(H) := by
  rintro e he
  ext x
  exact hHG.isNonloopAt_congr he

@[gcongr]
lemma Adj.mono (hHG : H ≤ G) (h : H.Adj x y) : G.Adj x y :=
  (h.choose_spec.mono hHG).adj

lemma le_iff_compatible_subset_subset : G ≤ H ↔ Compatible G H ∧ V(G) ⊆ V(H) ∧ E(G) ⊆ E(H) :=
  ⟨fun h ↦ ⟨.of_le h, h.1, h.edgeSet_mono⟩, fun ⟨h, hV, hE⟩ ↦
    ⟨hV, fun _ _ _ hxy ↦ h hxy.edge_mem (hE hxy.edge_mem) .. |>.mp hxy⟩⟩

lemma Compatible.le_iff (hH : Compatible H₁ H₂) : H₁ ≤ H₂ ↔ V(H₁) ⊆ V(H₂) ∧ E(H₁) ⊆ E(H₂) :=
  le_iff_compatible_subset_subset.trans (by tauto)

lemma Compatible.ext (hV : V(H₁) = V(H₂)) (hE : E(H₁) = E(H₂)) (h : Compatible H₁ H₂) : H₁ = H₂ :=
  (h.le_iff.mpr ⟨hV.subset, hE.subset⟩).antisymm <| h.symm.le_iff.mpr ⟨hV.superset, hE.superset⟩

lemma vertexSet_ssubset_or_edgeSet_ssubset_of_lt (hGH : G < H) : V(G) ⊂ V(H) ∨ E(G) ⊂ E(H) := by
  rw [lt_iff_le_and_ne] at hGH
  simp only [ssubset_iff_subset_ne, hGH.1.vertexSet_mono, ne_eq, true_and, hGH.1.edgeSet_mono]
  by_contra! heq
  exact hGH.2 <| hGH.1.compatible.ext heq.1 heq.2

@[simp]
lemma noEdge_le_iff : noEdge X β ≤ G ↔ X ⊆ V(G) := ⟨(·.vertexSet_mono), fun h ↦ ⟨h, by simp⟩⟩

@[simp]
lemma le_noEdge_iff : G ≤ noEdge X β ↔ V(G) ⊆ X ∧ E(G) = ∅ :=
  ⟨fun h ↦ ⟨h.vertexSet_mono, subset_empty_iff.1 h.edgeSet_mono⟩,
    fun h ↦ ⟨h.1, fun e x y he ↦ by simpa [h] using he.edge_mem⟩⟩

end Subgraph

section SpanningSubgraph

/-! ### Spanning Subgraphs -/

/-- `H ≤s G` (`Graph.IsSpanningSubgraph`) is a subgraph of `G` with the same vertex set. -/
@[mk_iff]
structure IsSpanningSubgraph (H G : Graph α β) : Prop extends le : H ≤ G where
  vertexSet_eq : V(H) = V(G)

@[inherit_doc IsSpanningSubgraph]
infixl:50 " ≤s " => Graph.IsSpanningSubgraph

namespace IsSpanningSubgraph

protected lemma trans (h₁ : G ≤s G₁) (h₂ : G₁ ≤s G₂) : G ≤s G₂ :=
  ⟨h₁.le.trans h₂.le, h₁.vertexSet_eq.trans h₂.vertexSet_eq⟩

instance : IsPartialOrder (Graph α β) (· ≤s ·) where
  refl G := ⟨le_refl G, rfl⟩
  trans _ _ _ h₁ h₂ := h₁.trans h₂
  antisymm _ _ h₁ h₂ := h₁.1.antisymm h₂.1

@[simp] protected lemma rfl : G ≤s G := refl G

lemma anti_right (hHK : H ≤ K) (hKG : K ≤ G) (h : H ≤s G) : H ≤s K where
  le := hHK
  vertexSet_eq := hHK.vertexSet_mono.antisymm <| hKG.vertexSet_mono.trans_eq h.vertexSet_eq.symm

lemma mono_left (hHK : H ≤ K) (hKG : K ≤ G) (h : H ≤s G) : K ≤s G where
  le := hKG
  vertexSet_eq := hKG.vertexSet_mono.antisymm <| h.vertexSet_eq.symm.le.trans hHK.vertexSet_mono

lemma ext_of_edgeSet (hE : E(H) = E(G)) (h : H ≤s G) : H = G :=
  h.compatible.ext h.vertexSet_eq hE

@[gcongr]
lemma banana_mono (hF : F₁ ⊆ F₂) : banana u v F₁ ≤s banana u v F₂ where
  vertexSet_eq := rfl

end IsSpanningSubgraph

end SpanningSubgraph

section InducedSubgraph

/-! ### Induced Subgraphs -/

/-- `H ≤i G` (`Graph.IsInducedSubgraph`) is a subgraph of `G` such that every link of `G`
involving two vertices of `H` is also a link of `H`. -/
@[mk_iff]
structure IsInducedSubgraph (H G : Graph α β) : Prop extends le : H ≤ G where
  isLink_of_mem_mem : ∀ ⦃e x y⦄, G.IsLink e x y → x ∈ V(H) → y ∈ V(H) → H.IsLink e x y

@[inherit_doc IsInducedSubgraph]
scoped infixl:50 " ≤i " => Graph.IsInducedSubgraph

namespace IsInducedSubgraph

protected lemma trans (h₁ : G ≤i G₁) (h₂ : G₁ ≤i G₂) : G ≤i G₂ :=
  ⟨h₁.le.trans h₂.le, fun _ _ _ h hx hy ↦ h₁.isLink_of_mem_mem
    (h₂.isLink_of_mem_mem h (h₁.vertexSet_mono hx) (h₁.vertexSet_mono hy)) hx hy⟩

instance : IsPartialOrder (Graph α β) (· ≤i ·) where
  refl G := ⟨le_refl G, by tauto⟩
  trans _ _ _ h₁ h₂ := h₁.trans h₂
  antisymm _ _ h₁ h₂ := h₁.1.antisymm h₂.1

@[simp] protected lemma rfl : G ≤i G := refl G

lemma isLink_congr (hx : x ∈ V(H)) (hy : y ∈ V(H)) (h : H ≤i G) :
    H.IsLink e x y ↔ G.IsLink e x y :=
  ⟨(·.mono h.le), fun hxy ↦ h.isLink_of_mem_mem hxy hx hy⟩

lemma adj_congr (hx : x ∈ V(H)) (hy : y ∈ V(H)) (h : H ≤i G) : H.Adj x y ↔ G.Adj x y :=
  ⟨(·.mono h.le), fun ⟨_, hxy⟩ ↦ (h.isLink_of_mem_mem hxy hx hy).adj⟩

lemma anti_right (hHK : H ≤ K) (hKG : K ≤ G) (h : H ≤i G) : H ≤i K where
  le := hHK
  isLink_of_mem_mem _ _ _ hxy hx hy := h.isLink_of_mem_mem (hxy.mono hKG) hx hy

lemma le_of_le_subset (h' : K ≤ G) (hsu : V(K) ⊆ V(H)) (h : H ≤i G) : K ≤ H := by
  refine (Compatible.of_le_le h' h.le).le_iff.mpr ⟨hsu, fun e he ↦ ?_⟩
  obtain ⟨u, v, huv⟩ := K.exists_isLink_of_mem_edgeSet he
  exact h.2 (huv.mono h') (hsu huv.left_mem) (hsu huv.right_mem) |>.edge_mem

lemma ext_of_vertexSet (hV : V(H) = V(G)) (h : H ≤i G) : H = G :=
  h.compatible.ext hV <| antisymm h.edgeSet_mono <| fun e he ↦ by
    obtain ⟨_, _, hxy⟩ := G.exists_isLink_of_mem_edgeSet he
    exact h.isLink_of_mem_mem hxy (hV ▸ hxy.left_mem) (hV ▸ hxy.right_mem) |>.edge_mem

end IsInducedSubgraph

lemma IsSubgraph.not_isInducedSubgraph_iff (hHG : H ≤ G) :
    ¬ H ≤i G ↔ ∃ e x y, G.IsLink e x y ∧ x ∈ V(H) ∧ y ∈ V(H) ∧ e ∉ E(H) := by
  contrapose!; symm
  exact ⟨fun hnind ↦ ⟨hHG, fun e x y hxy hx hy => hxy.anti_of_mem hHG (hnind e x y hxy hx hy)⟩,
    fun hind _ _ _ hexy hx hy ↦ hind.isLink_of_mem_mem hexy hx hy |>.edge_mem⟩

end InducedSubgraph

section ClosedSubgraph

/-! ### Closed Subgraphs -/

/-- `H ≤c G` (`Graph.IsClosedSubgraph`) is a union of components of `G`. -/
@[mk_iff]
structure IsClosedSubgraph (H G : Graph α β) : Prop extends
  isInducedSubgraph : IsInducedSubgraph H G where
  closed : ∀ ⦃e x⦄, G.Inc e x → x ∈ V(H) → e ∈ E(H)

@[inherit_doc IsClosedSubgraph]
scoped infixl:50 " ≤c " => Graph.IsClosedSubgraph

namespace IsClosedSubgraph

lemma mk' (hHG : H ≤ G) (hclosed : ∀ ⦃e x⦄, G.Inc e x → x ∈ V(H) → e ∈ E(H)) : H ≤c G where
  le := hHG
  isLink_of_mem_mem _ _ _ he hx _ := he.anti_of_mem hHG (hclosed he.inc_left hx)
  closed _ _ he hx := hclosed he hx

protected lemma trans (h₁ : G ≤c G₁) (h₂ : G₁ ≤c G₂) : G ≤c G₂ :=
  mk' (h₁.le.trans h₂.le) fun _ _ h hx ↦ h₁.closed (h.of_compatible h₂.compatible'
    (h₂.closed h (h₁.vertexSet_mono hx))) hx

instance : IsPartialOrder (Graph α β) (· ≤c ·) where
  refl _ := mk' le_rfl fun _ _ h _ ↦ h.edge_mem
  trans _ _ _ h₁ h₂ := h₁.trans h₂
  antisymm _ _ h₁ h₂ := h₁.le.antisymm h₂.le

@[simp] protected lemma rfl : G ≤c G := refl G

lemma inc_congr (hx : x ∈ V(H)) (hHG : H ≤c G) : H.Inc e x ↔ G.Inc e x :=
  ⟨(·.mono hHG.le), fun he ↦ he.of_compatible hHG.compatible' (hHG.closed he hx)⟩

lemma isLink_congr (hx : x ∈ V(H)) (hHG : H ≤c G) : H.IsLink e x y ↔ G.IsLink e x y :=
  ⟨(·.mono hHG.le), fun h ↦ h.anti_of_mem hHG.le ((hHG.inc_congr hx).mpr h.inc_left).edge_mem⟩

lemma mem_iff_of_isLink (he : G.IsLink e x y) (hHG : H ≤c G) : x ∈ V(H) ↔ y ∈ V(H) := by
  refine ⟨fun hin ↦ ?_, fun hin ↦ ?_⟩
  on_goal 2 => rw [isLink_comm] at he
  all_goals rw [← hHG.isLink_congr hin] at he; exact he.right_mem

lemma mem_tfae_of_isLink (he : G.IsLink e x y) (hHG : H ≤c G) :
    List.TFAE [x ∈ V(H), y ∈ V(H), e ∈ E(H)] := by
  tfae_have 1 → 2 := (hHG.mem_iff_of_isLink he).mp
  tfae_have 2 → 3 := (hHG.isLink_congr · |>.mpr he.symm |>.edge_mem)
  tfae_have 3 → 1 := (he.anti_of_mem hHG.le · |>.left_mem)
  tfae_finish

lemma adj_congr (hx : x ∈ V(H)) (hHG : H ≤c G) : H.Adj x y ↔ G.Adj x y :=
  ⟨(·.mono hHG.le), fun ⟨_, hxy⟩ ↦ (hHG.isLink_congr hx |>.mpr hxy).adj⟩

lemma mem_iff_of_adj (hxy : G.Adj x y) (hHG : H ≤c G) : x ∈ V(H) ↔ y ∈ V(H) :=
  hHG.mem_iff_of_isLink hxy.choose_spec

lemma anti_right (hHG₁ : H ≤ G₁) (hG₁ : G₁ ≤ G) (hHG : H ≤c G) : H ≤c G₁ :=
  mk' hHG₁ fun _ _ he hx ↦ hHG.inc_congr hx |>.mpr (he.mono hG₁) |>.edge_mem

end IsClosedSubgraph

lemma IsInducedSubgraph.not_isClosedSubgraph_iff_exists_adj (hHG : H ≤i G) :
    ¬ H ≤c G ↔ ∃ x y, G.Adj x y ∧ x ∈ V(H) ∧ y ∉ V(H) := by
  contrapose!; symm
  exact ⟨fun hncl ↦ ⟨hHG, fun e x ⟨y, hexy⟩ hxH =>
    hHG.isLink_of_mem_mem hexy hxH (hncl x y ⟨e, hexy⟩ hxH) |>.edge_mem⟩,
    fun hcl _ _ hexy ↦ (hcl.mem_iff_of_adj hexy).mp⟩

lemma IsInducedSubgraph.not_isClosedSubgraph_iff_exists_isLink (hHG : H ≤i G) :
    ¬ H ≤c G ↔ ∃ e x y, G.IsLink e x y ∧ x ∈ V(H) ∧ y ∉ V(H) := by
  rw [hHG.not_isClosedSubgraph_iff_exists_adj]
  unfold Adj
  tauto

end ClosedSubgraph

section OrderBot

instance : OrderBot (Graph α β) where
  bot := noEdge ∅ β
  bot_le G := by constructor <;> simp

instance : Inhabited (Graph α β) where
  default := ⊥

@[simp, grind =] lemma noEdge_empty : Graph.noEdge (∅ : Set α) β = ⊥ := rfl

@[simp] lemma vertexSet_bot : V((⊥ : Graph α β)) = ∅ := rfl

@[simp] lemma edgeSet_bot : E((⊥ : Graph α β)) = ∅ := rfl

@[simp] lemma bot_isClosedSubgraph (G : Graph α β) : ⊥ ≤c G := IsClosedSubgraph.mk' bot_le (by simp)

lemma eq_bot_or_vertexSet_nonempty (G : Graph α β) : G = ⊥ ∨ V(G).Nonempty := by
  refine (em (V(G) = ∅)).elim (fun he ↦ .inl (Graph.ext he fun e x y ↦ ?_)) (Or.inr ∘
    nonempty_iff_ne_empty.mpr)
  simp only [edgeSet_bot, mem_empty_iff_false, not_false_eq_true, not_isLink_of_notMem_edgeSet,
    iff_false]
  exact fun h ↦ by simpa [he] using h.left_mem

lemma vertexSet_eq_empty_iff : V(G) = ∅ ↔ G = ⊥ := by
  refine ⟨fun h ↦ bot_le.antisymm' ⟨by simp [h], fun e x y he ↦ ?_⟩, fun h ↦ by simp [h]⟩
  simpa [h] using he.left_mem

@[push, simp]
lemma ne_bot_iff : G ≠ ⊥ ↔ V(G).Nonempty :=
  not_iff_not.mp <| by simp [vertexSet_eq_empty_iff, not_nonempty_iff_eq_empty]

@[push, simp]
lemma vertexSet_not_nonempty_iff : ¬ V(G).Nonempty ↔ G = ⊥ := by
  simp [vertexSet_eq_empty_iff, not_nonempty_iff_eq_empty]

lemma ne_bot_of_mem_vertexSet (h : x ∈ V(G)) : G ≠ ⊥ := ne_bot_iff.mpr ⟨x, h⟩

@[simp]
lemma isSpanningSubgraph_bot_iff : G ≤s ⊥ ↔ G = ⊥ :=
  ⟨fun h => le_bot_iff.mp h.le, fun h => h ▸ .rfl⟩

@[simp]
lemma isInducedSubgraph_bot_iff : G ≤i ⊥ ↔ G = ⊥ :=
  ⟨fun h => le_bot_iff.mp h.le, fun h => h ▸ .rfl⟩

@[simp]
lemma isClosedSubgraph_bot_iff : G ≤c ⊥ ↔ G = ⊥ :=
  ⟨fun h => le_bot_iff.mp h.le, fun h => h ▸ .rfl⟩

lemma not_disjoint_of_mem_mem (h : x ∈ V(G)) (h' : x ∈ V(H)) : ¬ Disjoint G H := by
  simp only [Disjoint, le_bot_iff, not_forall, ne_eq, ne_bot_iff]
  use noEdge {x} β
  simp [h, h']

end OrderBot

end Graph
