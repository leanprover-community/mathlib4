/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Mathlib.Combinatorics.HypergraphLike.Basic

/-!
# Subgraphs of hypergraph-like structures

`HyperGraphLike.IsSubgraph H G` is a general notion of sub(hyper)graph. Between two graphs or
between two digraphs, it is the expected subgraph relation. Between two hypergraphs, it is the
*strong* subhypergraph relation where each edge is either deleted or all incidences of the edge are
retained. It also permits comparison between directed and undirected (hyper)graphs: a directed graph
with a single directed edge `e` from `u` to `v` is a subgraph of the undirected graph with an edge
`e` between `u` and `v`.
-/

@[expose] public section

open Set Function

namespace HyperGraphLike

variable {V I E Gr Gr₂ Gr₃ : Type*} {H : Gr} {G : Gr₂} {K : Gr₃} {i : I} {e : E}
  [HyperGraphLike V I E Gr] [HyperGraphLike V I E Gr₂] [HyperGraphLike V I E Gr₃] {u v : V}

/-- A subgraph retains whole edges, including all their incidences and attached vertices, and
preserves their permitted directions. A directed edge may become undirected in the larger graph. -/
structure IsSubgraph (H : Gr) (G : Gr₂) : Prop where
  /-- Every vertex of `H` is a vertex of `G`. -/
  verts_mono : V(H) ⊆ V(G)
  /-- Every edge of `H` is an edge of `G`. -/
  edges_mono : E(H) ⊆ E(G)
  /-- Every edge of `H` has exactly the same incidences in `G`. -/
  edgeFiber_eq ⦃e : E⦄ : e ∈ E(H) → edgeFiber H e = edgeFiber G e
  /-- Every incidence of `H` has the same attached vertex in `G`. -/
  attach'_eq ⦃i : I⦄ (hiH : i ∈ I(H)) (hiG : i ∈ I(G)) :
    (attach' H ⟨i, hiH⟩ : V) = (attach' G ⟨i, hiG⟩ : V)
  /-- Every source incidence of `H` is a source incidence of `G`. -/
  isSource_mono ⦃i : I⦄ : IsSource H i → IsSource G i
  /-- Every target incidence of `H` is a target incidence of `G`. -/
  isTarget_mono ⦃i : I⦄ : IsTarget H i → IsTarget G i

namespace IsSubgraph

lemma incs_mono (hHG : IsSubgraph H G) : I(H) ⊆ I(G) :=
  fun _ hi ↦ (mem_incs_iff.mp hi).elim
    (fun hs ↦ (hHG.isSource_mono hs).mem_incs) (fun ht ↦ (hHG.isTarget_mono ht).mem_incs)

attribute [gcongr only, grind →] verts_mono edges_mono incs_mono

/-! ### The subgraph relation -/

@[simp]
protected lemma rfl : IsSubgraph H H where
  verts_mono := .rfl
  edges_mono := .rfl
  edgeFiber_eq _ _ := rfl
  attach'_eq _ _ _ := rfl
  isSource_mono _ h := h
  isTarget_mono _ h := h

protected lemma refl (H : Gr) : IsSubgraph H H := .rfl

/-- Subgraph inclusion composes across different representation types. -/
protected lemma trans (hHG : IsSubgraph H G) (hGK : IsSubgraph G K) : IsSubgraph H K where
  verts_mono := hHG.verts_mono.trans hGK.verts_mono
  edges_mono := hHG.edges_mono.trans hGK.edges_mono
  edgeFiber_eq _ he := (hHG.edgeFiber_eq he).trans (hGK.edgeFiber_eq (hHG.edges_mono he))
  attach'_eq _ hiH hiK := (hHG.attach'_eq hiH (hHG.incs_mono hiH)).trans
    (hGK.attach'_eq (hHG.incs_mono hiH) hiK)
  isSource_mono _ h := hGK.isSource_mono (hHG.isSource_mono h)
  isTarget_mono _ h := hGK.isTarget_mono (hHG.isTarget_mono h)

instance : IsPreorder Gr (IsSubgraph : Gr → Gr → Prop) where
  refl _ := .rfl
  trans _ _ _ := .trans

instance : Trans (IsSubgraph : Gr → Gr₂ → Prop) (IsSubgraph : Gr₂ → Gr₃ → Prop)
    (IsSubgraph : Gr → Gr₃ → Prop) where
  trans := .trans

/-- Reverse inclusion holds exactly when the vertex and edge sets and directedness agree.
Equal ground sets alone do not suffice. -/
lemma antisymm_iff (hHG : IsSubgraph H G) :
    IsSubgraph G H ↔ V(H) = V(G) ∧ E(H) = E(G) ∧
      (∀ i, IsSource H i ↔ IsSource G i) ∧ (∀ i, IsTarget H i ↔ IsTarget G i) :=
  ⟨fun hGH ↦ ⟨hHG.verts_mono.antisymm hGH.verts_mono, hHG.edges_mono.antisymm hGH.edges_mono,
    fun _ ↦ ⟨(hHG.isSource_mono ·), (hGH.isSource_mono ·)⟩,
    fun _ ↦ ⟨(hHG.isTarget_mono ·), (hGH.isTarget_mono ·)⟩⟩, fun ⟨hV, hE, hS, hT⟩ ↦
    ⟨hV.superset, hE.superset, fun _ he ↦ (hHG.edgeFiber_eq (hE.superset he)).symm,
    fun _ hiG hiH ↦ (hHG.attach'_eq hiH hiG).symm, (hS · |>.mpr), (hT · |>.mpr)⟩⟩

/-! ### Incidence maps and orientation -/

variable (hHG : IsSubgraph H G)

include hHG

lemma edgeMap'_eq (hiH : i ∈ I(H)) (hiG : i ∈ I(G)) :
    (edgeMap' H ⟨i, hiH⟩ : E) = (edgeMap' G ⟨i, hiG⟩ : E) := by
  obtain ⟨_, he, rfl⟩ :=
    (hHG.edgeFiber_eq (edgeMap' H ⟨i, hiH⟩).property).subset ⟨⟨i, hiH⟩, rfl, rfl⟩
  exact he.symm

/-- Inclusion map of an incidence into the larger graph preserves the edge to which it belongs. -/
@[simp]
lemma edgeMap'_inclusion (i : I(H)) :
    edgeMap' G (inclusion hHG.incs_mono i) = inclusion hHG.edges_mono (edgeMap' H i) :=
  Subtype.ext (hHG.edgeMap'_eq i.property (hHG.incs_mono i.property)).symm

/-- Inclusion map of an incidence into the larger graph preserves its attached vertex. -/
@[simp]
lemma attach'_inclusion (i : I(H)) :
    attach' G (inclusion hHG.incs_mono i) = inclusion hHG.verts_mono (attach' H i) :=
  Subtype.ext (hHG.attach'_eq i.property (hHG.incs_mono i.property)).symm

lemma edgeMap_eq [Nonempty E] (hi : i ∈ I(H)) : edgeMap H i = edgeMap G i := by
  simpa using hHG.edgeMap'_eq hi (hHG.incs_mono hi)

lemma attach_eq [Nonempty V] (hi : i ∈ I(H)) : attach H i = attach G i := by
  simpa using hHG.attach'_eq hi (hHG.incs_mono hi)

end IsSubgraph

/-- A subgraph characterization using `attach`. -/
lemma isSubgraph_iff [Nonempty V] :
    IsSubgraph H G ↔ V(H) ⊆ V(G) ∧ E(H) ⊆ E(G) ∧
      (∀ e ∈ E(H), edgeFiber H e = edgeFiber G e) ∧ EqOn (attach H) (attach G) I(H) ∧
      (∀ i, IsSource H i → IsSource G i) ∧ (∀ i, IsTarget H i → IsTarget G i) :=
  ⟨fun h ↦ ⟨h.verts_mono, h.edges_mono, fun _ he ↦ h.edgeFiber_eq he, fun _ ↦ h.attach_eq,
    h.isSource_mono, h.isTarget_mono⟩,
    fun ⟨hV, hE, hF, hA, hS, hT⟩ ↦ ⟨hV, hE, hF, fun _ hi _ ↦ by simpa using hA hi, hS, hT⟩⟩

@[gcongr only]
lemma IsSource.mono (hHG : IsSubgraph H G) (h : IsSource H i) : IsSource G i :=
  hHG.isSource_mono h

@[gcongr only]
lemma IsTarget.mono (hHG : IsSubgraph H G) (h : IsTarget H i) : IsTarget G i :=
  hHG.isTarget_mono h

namespace Link

/-- A link in a subgraph gives a link in the larger graph with the same chosen incidences. -/
def mono (l : Link H e u v) (hHG : IsSubgraph H G) : Link G e u v where
  source := inclusion hHG.incs_mono l.source
  target := inclusion hHG.incs_mono l.target
  ne := (inclusion_injective hHG.incs_mono).ne l.ne
  isSource := hHG.isSource_mono l.isSource
  isTarget := hHG.isTarget_mono l.isTarget
  source_edge := (hHG.edgeMap'_eq l.source.property _).symm.trans l.source_edge
  target_edge := (hHG.edgeMap'_eq l.target.property _).symm.trans l.target_edge
  source_vertex := (hHG.attach'_eq l.source.property _).symm.trans l.source_vertex
  target_vertex := (hHG.attach'_eq l.target.property _).symm.trans l.target_vertex

@[simp]
lemma mono_source (l : Link H e u v) (hHG : IsSubgraph H G) :
    (l.mono hHG).source = inclusion hHG.incs_mono l.source := rfl

@[simp]
lemma mono_target (l : Link H e u v) (hHG : IsSubgraph H G) :
    (l.mono hHG).target = inclusion hHG.incs_mono l.target := rfl

@[simp]
lemma mono_rfl (l : Link H e u v) : l.mono (.rfl : IsSubgraph H H) = l := rfl

@[simp]
lemma mono_trans (l : Link H e u v) (hHG : IsSubgraph H G) (hGK : IsSubgraph G K) :
    (l.mono hHG).mono hGK = l.mono (hHG.trans hGK) := rfl

lemma mono_injective (hHG : IsSubgraph H G) : Injective (fun l : Link H e u v ↦ l.mono hHG) :=
  fun _ _ h ↦ Link.ext ((inclusion_injective hHG.incs_mono) (congrArg Link.source h))
    ((inclusion_injective hHG.incs_mono) (congrArg Link.target h))

@[simp]
lemma mono_inj (hHG : IsSubgraph H G) {l₁ l₂ : Link H e u v} :
    l₁.mono hHG = l₂.mono hHG ↔ l₁ = l₂ := (mono_injective hHG).eq_iff

end Link

@[gcongr only]
lemma IsLink.mono (hHG : IsSubgraph H G) (h : IsLink H e u v) : IsLink G e u v :=
  h.map (·.mono hHG)

@[gcongr only]
lemma Adj.mono (hHG : IsSubgraph H G) (h : Adj H u v) : Adj G u v :=
  h.elim fun _ he ↦ (he.mono hHG).adj

/-! ### Fibers and incident vertices and edges -/

namespace IsSubgraph

variable (hHG : IsSubgraph H G)

include hHG

@[gcongr only]
lemma edgeFiber_mono : edgeFiber H e ⊆ edgeFiber G e :=
  fun _ hi ↦ (hHG.edgeFiber_eq (mem_edges_of_mem_edgeFiber hi)).subset hi

@[gcongr only]
lemma vertexFiber_mono : vertexFiber H v ⊆ vertexFiber G v := by
  rintro i ⟨j, hj, rfl⟩
  exact ⟨inclusion hHG.incs_mono j, (hHG.attach'_eq j.property _).symm.trans hj, rfl⟩

lemma edgeFiber_eq_inter : edgeFiber H e = I(H) ∩ edgeFiber G e := by
  let : Nonempty E := ⟨e⟩
  ext i
  simp only [mem_inter_iff, mem_edgeFiber]
  refine and_congr_right fun hi ↦ ?_
  rw [hHG.edgeMap_eq hi, and_iff_right (hHG.incs_mono hi)]

lemma vertexFiber_eq_inter : vertexFiber H v = I(H) ∩ vertexFiber G v := by
  let : Nonempty V := ⟨v⟩
  ext i
  simp only [mem_inter_iff, mem_vertexFiber]
  refine and_congr_right fun hi ↦ ?_
  rw [hHG.attach_eq hi, and_iff_right (hHG.incs_mono hi)]

/-- A retained edge has the same incident vertices. -/
lemma incVerts_eq (he : e ∈ E(H)) : incVerts H e = incVerts G e := by
  ext v
  let : Nonempty V := ⟨v⟩
  rw [incVerts_eq_image, incVerts_eq_image, ← hHG.edgeFiber_eq he,
    image_congr (fun _ hi ↦ hHG.attach_eq (edgeFiber_subset_incs hi))]

@[gcongr only]
lemma incVerts_mono : incVerts H e ⊆ incVerts G e :=
  fun _ hv ↦ (hHG.incVerts_eq (mem_edges_of_mem_incVerts hv)).subset hv

/-- The edges at a vertex in `H` are exactly edges at that vertex in `G` that also exists in `H`. -/
lemma incEdges_eq_inter : incEdges H v = E(H) ∩ incEdges G v :=
  Set.ext fun _ ↦ (and_iff_right_of_imp (incEdges_subset_edges ·)).symm.trans
    (and_congr_right fun he ↦ by simp only [mem_incEdges, hHG.incVerts_eq he])

@[gcongr only]
lemma incEdges_mono : incEdges H v ⊆ incEdges G v :=
  hHG.incEdges_eq_inter.subset.trans inter_subset_right

/-- An incidence of `G` belongs to `H` exactly when its edge belongs to `H`. -/
lemma mem_incs_iff [Nonempty E] (hi : i ∈ I(G)) : i ∈ I(H) ↔ edgeMap G i ∈ E(H) :=
  ⟨fun hiH ↦ hHG.edgeMap_eq hiH ▸ edgeMap_mem_edges hiH,
    fun he ↦ edgeFiber_subset_incs ((hHG.edgeFiber_eq he).superset (mem_edgeFiber.mpr ⟨hi, rfl⟩))⟩

lemma incs_eq_inter_preimage [Nonempty E] : I(H) = I(G) ∩ edgeMap G ⁻¹' E(H) :=
  Set.ext fun _ ↦ (and_iff_right_of_imp (hHG.incs_mono ·)).symm.trans
    (and_congr_right fun hi ↦ hHG.mem_incs_iff hi)

/-- Keeping all edges keeps all incidences, even though directedness may change. -/
lemma incs_eq_of_edges_eq (hE : E(H) = E(G)) : I(H) = I(G) := by
  rw [← biUnion_edgeFiber H, ← biUnion_edgeFiber G, ← hE]
  exact iUnion₂_congr fun _ he ↦ hHG.edgeFiber_eq he

lemma edgeFiber_eq_iff : edgeFiber H e = edgeFiber G e ↔ edgeFiber G e ⊆ I(H) := by
  rw [hHG.edgeFiber_eq_inter, inter_eq_right]

lemma vertexFiber_eq_iff : vertexFiber H v = vertexFiber G v ↔ vertexFiber G v ⊆ I(H) := by
  rw [hHG.vertexFiber_eq_inter, inter_eq_right]

end IsSubgraph

end HyperGraphLike
