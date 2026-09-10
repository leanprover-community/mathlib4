/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Mathlib.Combinatorics.IncidenceHypergraph.Basic
public import Mathlib.Data.Set.Inclusion

/-!
# Subgraphs of incidence hypergraphs

## Main definitions

* `H ≤ G`: inclusion of the three active sets, preserving the edge and vertex of each retained
  incidence. This is the preferred spelling over `H.IsSubgraph G`.
* `IncidenceHypergraph.Compatible`: shared incidence labels have the same assignments.
* `IncidenceHypergraph.noIncidence`: specified vertex and edge sets with no incidences.
* `⊥`: the hypergraph with no vertices, incidences, or edges.

## Implementation notes

As for `Graph`, subgraphs have the same type as the ambient hypergraph. The `IsSubgraph` proposition
supplies the partial order and can be extended by stronger subgraph notions. The API uses `≤` as
its normal form. Inclusions between the active subtypes use `Set.inclusion`.

A subhypergraph may retain only some or zero incidences of an edge. Consequently, retaining an edge
does not imply reflection of `endSet` or `IsLink`. Compatibility compares the assignments of shared
incidence labels, preserving their identities.
-/

@[expose] public section

open Set

namespace IncidenceHypergraph

variable {ν ι ε : Type*} {G H K G₁ G₂ H₁ H₂ : IncidenceHypergraph ν ι ε} {e : ε} {u v : ν} {i j : ι}

/-! ### Subgraph order -/

/-- Inclusion of the active sets, preserving both assignments of each retained incidence.
Use `H ≤ G` in statements instead of `H.IsSubgraph G`. -/
@[mk_iff]
structure IsSubgraph (H G : IncidenceHypergraph ν ι ε) : Prop where
  vertexSet_mono : V(H) ⊆ V(G)
  incidenceSet_mono : I(H) ⊆ I(G)
  edgeSet_mono : E(H) ⊆ E(G)
  edgeMap'_eq : ∀ i : I(H), G.edgeMap' (Set.inclusion incidenceSet_mono i) = H.edgeMap' i
  attach'_eq : ∀ i : I(H), G.attach' (Set.inclusion incidenceSet_mono i) = H.attach' i

attribute [gcongr, grind →] IsSubgraph.vertexSet_mono IsSubgraph.incidenceSet_mono
  IsSubgraph.edgeSet_mono

lemma IsSubgraph.refl (G : IncidenceHypergraph ν ι ε) : G.IsSubgraph G where
  vertexSet_mono := Subset.rfl
  incidenceSet_mono := Subset.rfl
  edgeSet_mono := Subset.rfl
  edgeMap'_eq _ := rfl
  attach'_eq _ := rfl

@[trans]
lemma IsSubgraph.trans (hHG : H.IsSubgraph G) (hGK : G.IsSubgraph K) : H.IsSubgraph K where
  vertexSet_mono := hHG.vertexSet_mono.trans hGK.vertexSet_mono
  incidenceSet_mono := hHG.incidenceSet_mono.trans hGK.incidenceSet_mono
  edgeSet_mono := hHG.edgeSet_mono.trans hGK.edgeSet_mono
  edgeMap'_eq i :=
    (hGK.edgeMap'_eq (Set.inclusion hHG.incidenceSet_mono i)).trans (hHG.edgeMap'_eq i)
  attach'_eq i := (hGK.attach'_eq (Set.inclusion hHG.incidenceSet_mono i)).trans (hHG.attach'_eq i)

lemma IsSubgraph.antisymm (hHG : H.IsSubgraph G) (hGH : G.IsSubgraph H) : H = G :=
  IncidenceHypergraph.ext (hHG.vertexSet_mono.antisymm hGH.vertexSet_mono)
    (hHG.incidenceSet_mono.antisymm hGH.incidenceSet_mono)
    (hHG.edgeSet_mono.antisymm hGH.edgeSet_mono)
    (fun i hiH _ ↦ (hHG.edgeMap'_eq ⟨i, hiH⟩).symm)
    (fun i hiH _ ↦ (hHG.attach'_eq ⟨i, hiH⟩).symm)

/-- The order retaining incidence labels and their original assignments. -/
instance : PartialOrder (IncidenceHypergraph ν ι ε) where
  le := IsSubgraph
  le_refl := IsSubgraph.refl
  le_trans _ _ _ := IsSubgraph.trans
  le_antisymm _ _ := IsSubgraph.antisymm

@[simp]
lemma isSubgraph_iff_le : H.IsSubgraph G ↔ H ≤ G := Iff.rfl

lemma IsSubgraph.edgeMap_eq_of_mem [Nonempty ε] (hHG : H ≤ G) (hiH : i ∈ I(H)) (hiG : i ∈ I(G)) :
    H.edgeMap i = G.edgeMap i := by
  rw [← H.edgeMap'_eq_edgeMap ⟨i, hiH⟩, ← G.edgeMap'_eq_edgeMap ⟨i, hiG⟩]
  exact (hHG.edgeMap'_eq ⟨i, hiH⟩).symm

lemma IsSubgraph.attach'_eq_of_mem [Nonempty ν] (hHG : H ≤ G) (hiH : i ∈ I(H)) (hiG : i ∈ I(G)) :
    H.attach i = G.attach i := by
  rw [← H.attach'_eq_attach ⟨i, hiH⟩, ← G.attach'_eq_attach ⟨i, hiG⟩]
  exact (hHG.attach'_eq ⟨i, hiH⟩).symm

lemma IsSubgraph.edgeMap_comp_inclusion (hHG : H ≤ G) :
    G.edgeMap' ∘ Set.inclusion hHG.incidenceSet_mono = H.edgeMap' :=
  funext hHG.edgeMap'_eq

lemma IsSubgraph.attach_comp_inclusion (hHG : H ≤ G) :
    G.attach' ∘ Set.inclusion hHG.incidenceSet_mono = H.attach' :=
  funext hHG.attach'_eq

@[gcongr]
lemma IsSubgraph.endSet_mono (hHG : H ≤ G) : H.endSet e ⊆ G.endSet e := by
  rintro w ⟨i, he, rfl⟩
  exact ⟨Set.inclusion hHG.incidenceSet_mono i, (hHG.edgeMap'_eq i).trans he, hHG.attach'_eq i⟩

@[gcongr]
lemma IsLink.mono (hHG : H ≤ G) (h : H.IsLink e u v) : G.IsLink e u v := by
  obtain ⟨i, j, hij, hi, hj, hu, hv⟩ := h
  exact ⟨Set.inclusion hHG.incidenceSet_mono i, Set.inclusion hHG.incidenceSet_mono j,
    fun h ↦ hij (Set.inclusion_injective _ h), (hHG.edgeMap'_eq i).trans hi,
    (hHG.edgeMap'_eq j).trans hj, (hHG.attach'_eq i).trans hu, (hHG.attach'_eq j).trans hv⟩

@[gcongr]
lemma Adj.mono (hHG : H ≤ G) (h : H.Adj u v) : G.Adj u v :=
  h.imp fun _ he ↦ he.mono hHG

/-! ### Compatibility -/

/-- Two incidence hypergraphs are compatible when every shared incidence label has the same
edge and attached vertex in both hypergraphs. -/
@[mk_iff]
structure Compatible (G H : IncidenceHypergraph ν ι ε) : Prop where
  edgeMap_eq : ∀ ⦃i⦄ (hiG : i ∈ I(G)) (hiH : i ∈ I(H)), G.edgeMap' ⟨i, hiG⟩ = H.edgeMap' ⟨i, hiH⟩
  attach_eq : ∀ ⦃i⦄ (hiG : i ∈ I(G)) (hiH : i ∈ I(H)), G.attach' ⟨i, hiG⟩ = H.attach' ⟨i, hiH⟩

@[simp]
lemma Compatible.rfl : G.Compatible G where
  edgeMap_eq _ _ _ := Eq.refl _
  attach_eq _ _ _ := Eq.refl _

instance : Std.Refl (Compatible : IncidenceHypergraph ν ι ε → _ → Prop) where
  refl _ := Compatible.rfl

@[symm]
lemma Compatible.symm (h : G.Compatible H) : H.Compatible G where
  edgeMap_eq _ hiH hiG := (h.edgeMap_eq hiG hiH).symm
  attach_eq _ hiH hiG := (h.attach_eq hiG hiH).symm

instance : Std.Symm (Compatible : IncidenceHypergraph ν ι ε → _ → Prop) where
  symm _ _ := Compatible.symm

lemma compatible_comm : G.Compatible H ↔ H.Compatible G :=
  ⟨Compatible.symm, Compatible.symm⟩

lemma Compatible.of_disjoint_incidenceSet (h : Disjoint I(G) I(H)) : G.Compatible H where
  edgeMap_eq _ hiG hiH := (Set.disjoint_left.mp h hiG hiH).elim
  attach_eq _ hiG hiH := (Set.disjoint_left.mp h hiG hiH).elim

lemma Compatible.of_le_le (hHG : H ≤ G) (hKG : K ≤ G) : H.Compatible K where
  edgeMap_eq _ hiH hiK := (hHG.edgeMap'_eq ⟨_, hiH⟩).symm.trans (hKG.edgeMap'_eq ⟨_, hiK⟩)
  attach_eq _ hiH hiK := (hHG.attach'_eq ⟨_, hiH⟩).symm.trans (hKG.attach'_eq ⟨_, hiK⟩)

lemma IsSubgraph.compatible (hHG : H ≤ G) : H.Compatible G :=
  Compatible.of_le_le hHG le_rfl

lemma Compatible.anti_left (hG₁G : G₁ ≤ G) (h : G.Compatible H) : G₁.Compatible H where
  edgeMap_eq _ hiG₁ hiH := (hG₁G.edgeMap'_eq ⟨_, hiG₁⟩).symm.trans
    (h.edgeMap_eq (hG₁G.incidenceSet_mono hiG₁) hiH)
  attach_eq _ hiG₁ hiH := (hG₁G.attach'_eq ⟨_, hiG₁⟩).symm.trans
    (h.attach_eq (hG₁G.incidenceSet_mono hiG₁) hiH)

lemma Compatible.anti_right (hH₁H : H₁ ≤ H) (h : G.Compatible H) : G.Compatible H₁ :=
  (h.symm.anti_left hH₁H).symm

lemma Compatible.anti (hG₁G : G₁ ≤ G) (hH₁H : H₁ ≤ H) (h : G.Compatible H) : G₁.Compatible H₁ :=
  (h.anti_left hG₁G).anti_right hH₁H

@[grind =]
lemma le_iff_compatible_subset_subset_subset :
    G ≤ H ↔ G.Compatible H ∧ V(G) ⊆ V(H) ∧ I(G) ⊆ I(H) ∧ E(G) ⊆ E(H) :=
  ⟨fun h ↦ ⟨h.compatible, h.vertexSet_mono, h.incidenceSet_mono, h.edgeSet_mono⟩,
    fun ⟨h, hV, hI, hE⟩ ↦ ⟨hV, hI, hE, fun i ↦ (h.edgeMap_eq i.property (hI i.property)).symm,
      fun i ↦ (h.attach_eq i.property (hI i.property)).symm⟩⟩

lemma Compatible.ext (hV : V(G) = V(H)) (hI : I(G) = I(H)) (hE : E(G) = E(H)) (h : G.Compatible H) :
    G = H :=
  IncidenceHypergraph.ext hV hI hE (fun _ hiG hiH ↦ h.edgeMap_eq hiG hiH)
    (fun _ hiG hiH ↦ h.attach_eq hiG hiH)

lemma vertexSet_ssubset_or_incidenceSet_ssubset_or_edgeSet_ssubset_of_lt (h : G < H) :
    V(G) ⊂ V(H) ∨ I(G) ⊂ I(H) ∨ E(G) ⊂ E(H) := by
  grind [ssubset_iff_subset_not_subset, Compatible.ext, h.le, h.ne]

/-! ### Hypergraphs with no incidences -/

variable {V : Set ν} {E : Set ε}

/-- The incidence hypergraph with the given vertex and edge sets and no incidences.
All of its vertices and edges are isolated. -/
@[simps vertexSet incidenceSet edgeSet]
def noIncidence (V : Set ν) (E : Set ε) (ι : Type*) : IncidenceHypergraph ν ι ε where
  vertexSet := V
  incidenceSet := ∅
  edgeSet := E
  edgeMap' i := i.property.elim
  edgeMap'_mem i := i.property.elim
  attach' i := i.property.elim
  attach'_mem i := i.property.elim

lemma incidenceSet_eq_empty : I(G) = ∅ ↔ G = noIncidence V(G) E(G) ι :=
  ⟨fun h ↦ IncidenceHypergraph.ext rfl h rfl (fun _ hi _ ↦ (h ▸ hi).elim)
    (fun _ hi _ ↦ (h ▸ hi).elim), fun h ↦ congrArg incidenceSet h⟩

@[simp]
lemma endSet_noIncidence (V : Set ν) (E : Set ε) (ι : Type*) (e : ε) :
    (noIncidence V E ι).endSet e = ∅ := by
  ext v
  simp [endSet, noIncidence]

@[simp]
lemma noIncidence_isLink (V : Set ν) (E : Set ε) (ι : Type*) (e : ε) (u v : ν) :
    ¬ (noIncidence V E ι).IsLink e u v := by
  simp [IsLink, noIncidence]

@[simp]
lemma noIncidence_adj (V : Set ν) (E : Set ε) (ι : Type*) (u v : ν) :
    ¬ (noIncidence V E ι).Adj u v := by
  simp [Adj]

@[simp]
lemma noIncidence_le_iff : noIncidence V E ι ≤ G ↔ V ⊆ V(G) ∧ E ⊆ E(G) :=
  ⟨fun h ↦ ⟨h.vertexSet_mono, h.edgeSet_mono⟩,
    fun ⟨hV, hE⟩ ↦ ⟨hV, empty_subset _, hE, fun i ↦ i.property.elim, fun i ↦ i.property.elim⟩⟩

@[simp]
lemma le_noIncidence_iff : G ≤ noIncidence V E ι ↔ V(G) ⊆ V ∧ E(G) ⊆ E ∧ I(G) = ∅ :=
  ⟨fun h ↦ ⟨h.vertexSet_mono, h.edgeSet_mono, subset_empty_iff.mp h.incidenceSet_mono⟩,
    fun ⟨hV, hE, hI⟩ ↦ ⟨hV, by simp [hI], hE,
      fun i ↦ (Set.notMem_empty i.val (hI ▸ i.property)).elim,
      fun i ↦ (Set.notMem_empty i.val (hI ▸ i.property)).elim⟩⟩

@[simp]
lemma noIncidence_compatible (G : IncidenceHypergraph ν ι ε) : (noIncidence V E ι).Compatible G :=
  Compatible.of_disjoint_incidenceSet (by simp)

@[simp]
lemma compatible_noIncidence (G : IncidenceHypergraph ν ι ε) : G.Compatible (noIncidence V E ι) :=
  (noIncidence_compatible G).symm

/-! ### Bottom -/

/-- The incidence hypergraph with no vertices, incidences, or edges. -/
instance : OrderBot (IncidenceHypergraph ν ι ε) where
  bot := noIncidence ∅ ∅ ι
  bot_le _ := noIncidence_le_iff.mpr ⟨empty_subset _, empty_subset _⟩

instance : Inhabited (IncidenceHypergraph ν ι ε) where
  default := ⊥

@[simp]
lemma vertexSet_bot : V((⊥ : IncidenceHypergraph ν ι ε)) = ∅ :=
  rfl

@[simp]
lemma incidenceSet_bot : I((⊥ : IncidenceHypergraph ν ι ε)) = ∅ :=
  rfl

@[simp]
lemma edgeSet_bot : E((⊥ : IncidenceHypergraph ν ι ε)) = ∅ :=
  rfl

@[simp]
lemma noIncidence_empty_empty : noIncidence (∅ : Set ν) (∅ : Set ε) ι = ⊥ :=
  rfl

@[simp, grind =]
lemma eq_bot_iff : V(G) = ∅ ∧ E(G) = ∅ ↔ G = ⊥ :=
  ⟨fun ⟨hV, hE⟩ ↦ le_bot_iff.mp (le_noIncidence_iff.mpr
    ⟨hV.subset, hE.subset, incidenceSet_eq_empty_of_vertexSet_eq_empty hV⟩), fun h ↦ by simp [h]⟩

@[simp]
lemma bot_compatible (G : IncidenceHypergraph ν ι ε) :
    (⊥ : IncidenceHypergraph ν ι ε).Compatible G := noIncidence_compatible G

@[simp]
lemma compatible_bot (G : IncidenceHypergraph ν ι ε) : G.Compatible ⊥ := (bot_compatible G).symm

/-- Isolated edges can witness that a hypergraph is nonempty even when it has no vertices. -/
@[simp]
lemma ne_bot_iff : G ≠ ⊥ ↔ V(G).Nonempty ∨ E(G).Nonempty := by
  simpa only [not_and_or, ← Set.nonempty_iff_ne_empty] using
    (IncidenceHypergraph.eq_bot_iff (G := G)).not.symm

lemma ne_bot_of_mem_vertexSet (h : u ∈ V(G)) : G ≠ ⊥ :=
  ne_bot_iff.mpr (Or.inl ⟨u, h⟩)

lemma ne_bot_of_mem_incidenceSet (h : i ∈ I(G)) : G ≠ ⊥ :=
  ne_bot_of_mem_vertexSet (G.attach'_mem ⟨i, h⟩)

lemma ne_bot_of_mem_edgeSet (h : e ∈ E(G)) : G ≠ ⊥ :=
  ne_bot_iff.mpr (Or.inr ⟨e, h⟩)

/-! ### Disjointness -/

/-- A common isolated vertex or isolated edge is already a nonbottom common subgraph.
Assignments on shared incidence labels may disagree, so incidence-set disjointness is not required.
-/
lemma disjoint_iff : Disjoint G H ↔ Disjoint V(G) V(H) ∧ Disjoint E(G) E(H) := by
  refine ⟨fun h ↦ ?_, fun ⟨hV, hE⟩ K hKG hKH ↦ le_bot_iff.mpr (eq_bot_iff.mp
    ⟨subset_empty_iff.mp (hV hKG.vertexSet_mono hKH.vertexSet_mono),
      subset_empty_iff.mp (hE hKG.edgeSet_mono hKH.edgeSet_mono)⟩)⟩
  have hle : noIncidence (V(G) ∩ V(H)) (E(G) ∩ E(H)) ι ≤ ⊥ :=
    h (noIncidence_le_iff.mpr ⟨inter_subset_left, inter_subset_left⟩)
      (noIncidence_le_iff.mpr ⟨inter_subset_right, inter_subset_right⟩)
  exact ⟨Set.disjoint_iff_inter_eq_empty.mpr (subset_empty_iff.mp hle.vertexSet_mono),
    Set.disjoint_iff_inter_eq_empty.mpr (subset_empty_iff.mp hle.edgeSet_mono)⟩

lemma not_disjoint_of_mem_vertexSet (huG : u ∈ V(G)) (huH : u ∈ V(H)) : ¬ Disjoint G H :=
  fun h ↦ Set.disjoint_left.mp (disjoint_iff.mp h).1 huG huH

lemma not_disjoint_of_mem_edgeSet (heG : e ∈ E(G)) (heH : e ∈ E(H)) : ¬ Disjoint G H :=
  fun h ↦ Set.disjoint_left.mp (disjoint_iff.mp h).2 heG heH

lemma Compatible.disjoint_incidenceSet_of_disjoint_vertexSet (h : G.Compatible H)
    (hV : Disjoint V(G) V(H)) : Disjoint I(G) I(H) :=
  Set.disjoint_left.mpr fun i hiG hiH ↦ Set.disjoint_left.mp hV (G.attach'_mem ⟨i, hiG⟩)
    (h.attach_eq hiG hiH ▸ H.attach'_mem ⟨i, hiH⟩)

lemma Compatible.disjoint_incidenceSet_of_disjoint_edgeSet (h : G.Compatible H)
    (hE : Disjoint E(G) E(H)) : Disjoint I(G) I(H) :=
  Set.disjoint_left.mpr fun i hiG hiH ↦ Set.disjoint_left.mp hE (G.edgeMap'_mem ⟨i, hiG⟩)
    (h.edgeMap_eq hiG hiH ▸ H.edgeMap'_mem ⟨i, hiH⟩)

end IncidenceHypergraph
