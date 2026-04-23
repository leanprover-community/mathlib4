/-
Copyright (c) 2020 Aaron Anderson, Jalex Stark, Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jalex Stark, Kyle Miller, Alena Gusakov, Hunter Monroe
-/
module

public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Combinatorics.SimpleGraph.Finite
import Batteries.Tactic.Trans
import Mathlib.Combinatorics.SimpleGraph.Init
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

/-!
# Edge deletion

This file defines operations deleting the edges of a simple graph and proves theorems in the finite
case.

## Main definitions

* `SimpleGraph.deleteEdges G s` is the simple graph `G` with the edges `s : Set (Sym2 V)` removed
  from the edge set.

* `SimpleGraph.deleteIncidenceSet G v` is the simple graph `G` with the incidence set of `v`
  removed from the edge set.

* `SimpleGraph.deleteFar G p r` is the predicate that a graph is `r`-*delete-far* from a property
  `p`, that is, at least `r` edges must be deleted to satisfy `p`.
-/

@[expose] public section


open Finset Fintype

namespace SimpleGraph

variable {V : Type*} {v w : V} (G : SimpleGraph V)

section DeleteEdges

/-- Given a set of vertex pairs, remove all of the corresponding edges from the
graph's edge set, if present.

See also: `SimpleGraph.Subgraph.deleteEdges`. -/
def deleteEdges (s : Set (Sym2 V)) : SimpleGraph V := G \ fromEdgeSet s

variable {G} {H : SimpleGraph V} {s s₁ s₂ : Set (Sym2 V)}

instance [DecidableRel G.Adj] [DecidablePred (· ∈ s)] [DecidableEq V] :
    DecidableRel (G.deleteEdges s).Adj :=
  inferInstanceAs <| DecidableRel (G \ fromEdgeSet s).Adj

@[simp] lemma deleteEdges_adj : (G.deleteEdges s).Adj v w ↔ G.Adj v w ∧ s(v, w) ∉ s :=
  and_congr_right fun h ↦ (and_iff_left h.ne).not

@[simp] lemma deleteEdges_edgeSet (G G' : SimpleGraph V) : G.deleteEdges G'.edgeSet = G \ G' := by
  ext; simp

@[simp]
theorem deleteEdges_deleteEdges (s s' : Set (Sym2 V)) :
    (G.deleteEdges s).deleteEdges s' = G.deleteEdges (s ∪ s') := by simp [deleteEdges, sdiff_sdiff]

-- This is not marked `simp` since `deleteEdges_of_subset_diagSet` already proves it
lemma deleteEdges_empty : G.deleteEdges ∅ = G := by simp [deleteEdges]
@[simp] lemma deleteEdges_univ : G.deleteEdges Set.univ = ⊥ := by simp [deleteEdges]

@[simp]
theorem deleteEdges_le_iff (s : Set (Sym2 V)) (G' : SimpleGraph V) :
    G.deleteEdges s ≤ G' ↔ G ≤ fromEdgeSet s ⊔ G' := by
    rw [deleteEdges, sdiff_le_iff]

lemma deleteEdges_le (s : Set (Sym2 V)) : G.deleteEdges s ≤ G := sdiff_le

lemma deleteEdges_anti (h : s₁ ⊆ s₂) : G.deleteEdges s₂ ≤ G.deleteEdges s₁ :=
  sdiff_le_sdiff_left <| fromEdgeSet_mono h

lemma deleteEdges_mono (h : G ≤ H) : G.deleteEdges s ≤ H.deleteEdges s := sdiff_le_sdiff_right h

@[simp] lemma deleteEdges_eq_self : G.deleteEdges s = G ↔ Disjoint G.edgeSet s := by
  rw [deleteEdges, sdiff_eq_left, disjoint_fromEdgeSet]

theorem deleteEdges_eq_inter_edgeSet (s : Set (Sym2 V)) :
    G.deleteEdges s = G.deleteEdges (s ∩ G.edgeSet) := by
  ext
  simp +contextual [imp_false]

@[simp] lemma deleteEdges_of_subset_diagSet (G : SimpleGraph V) (hs : s ⊆ Sym2.diagSet) :
    G.deleteEdges s = G := by ext u v; simpa using (·.ne <| hs ·)

theorem deleteEdges_sdiff_eq_of_le {H : SimpleGraph V} (h : H ≤ G) :
    G.deleteEdges (G.edgeSet \ H.edgeSet) = H := by
  rw [← edgeSet_sdiff, deleteEdges_edgeSet, sdiff_sdiff_eq_self h]

@[simp]
theorem edgeSet_deleteEdges (s : Set (Sym2 V)) : (G.deleteEdges s).edgeSet = G.edgeSet \ s := by
  simp [deleteEdges]

@[simp] theorem edgeFinset_deleteEdges [DecidableEq V] [Fintype G.edgeSet] (s : Finset (Sym2 V))
    [Fintype (G.deleteEdges s).edgeSet] :
    (G.deleteEdges s).edgeFinset = G.edgeFinset \ s := by
  ext e
  simp [edgeSet_deleteEdges]

@[simp] lemma deleteEdges_sup (G H : SimpleGraph V) (s : Set (Sym2 V)) :
    (G ⊔ H).deleteEdges s = G.deleteEdges s ⊔ H.deleteEdges s := sup_sdiff

@[simp] lemma deleteEdges_fromEdgeSet (s t : Set (Sym2 V)) :
    (fromEdgeSet s).deleteEdges t = fromEdgeSet (s \ t) := by ext; simp +contextual

@[simp] lemma deleteEdges_eq_bot : G.deleteEdges s = ⊥ ↔ G.edgeSet ⊆ s := by simp [deleteEdges]

end DeleteEdges

section DeleteIncidenceSet

/-- Given a vertex `x`, remove the edges incident to `x` from the edge set. -/
def deleteIncidenceSet (G : SimpleGraph V) (x : V) : SimpleGraph V :=
  G.deleteEdges (G.incidenceSet x)

lemma deleteIncidenceSet_adj {G : SimpleGraph V} {x v₁ v₂ : V} :
    (G.deleteIncidenceSet x).Adj v₁ v₂ ↔ G.Adj v₁ v₂ ∧ v₁ ≠ x ∧ v₂ ≠ x := by
  rw [deleteIncidenceSet, deleteEdges_adj, mk'_mem_incidenceSet_iff]
  tauto

lemma deleteIncidenceSet_le (G : SimpleGraph V) (x : V) : G.deleteIncidenceSet x ≤ G :=
  deleteEdges_le (G.incidenceSet x)

lemma edgeSet_fromEdgeSet_incidenceSet (G : SimpleGraph V) (x : V) :
    (fromEdgeSet (G.incidenceSet x)).edgeSet = G.incidenceSet x := by
  rw [edgeSet_fromEdgeSet, sdiff_eq_left, ← Set.subset_compl_iff_disjoint_right]
  exact (incidenceSet_subset G x).trans G.edgeSet_subset_compl_diagSet

/-- The edge set of `G.deleteIncidenceSet x` is the edge set of `G` set difference the incidence
set of the vertex `x`. -/
theorem edgeSet_deleteIncidenceSet (G : SimpleGraph V) (x : V) :
    (G.deleteIncidenceSet x).edgeSet = G.edgeSet \ G.incidenceSet x := by
  simp_rw [deleteIncidenceSet, deleteEdges, edgeSet_sdiff, edgeSet_fromEdgeSet_incidenceSet]

/-- The support of `G.deleteIncidenceSet x` is a subset of the support of `G` set difference the
singleton set `{x}`. -/
theorem support_deleteIncidenceSet_subset (G : SimpleGraph V) (x : V) :
    (G.deleteIncidenceSet x).support ⊆ G.support \ {x} :=
  fun _ ↦ by simp_rw [mem_support, deleteIncidenceSet_adj]; tauto

/-- If the vertex `x` is not in the set `s`, then the induced subgraph in `G.deleteIncidenceSet x`
by `s` is equal to the induced subgraph in `G` by `s`. -/
theorem induce_deleteIncidenceSet_of_notMem (G : SimpleGraph V) {s : Set V} {x : V} (h : x ∉ s) :
    (G.deleteIncidenceSet x).induce s = G.induce s := by
  ext v₁ v₂
  simp_rw [comap_adj, Function.Embedding.coe_subtype, deleteIncidenceSet_adj, and_iff_left_iff_imp]
  exact fun _ ↦ ⟨v₁.prop.ne_of_notMem h, v₂.prop.ne_of_notMem h⟩

variable [Fintype V] [DecidableEq V]

instance {G : SimpleGraph V} [DecidableRel G.Adj] {x : V} :
    DecidableRel (G.deleteIncidenceSet x).Adj :=
  inferInstanceAs <| DecidableRel (G.deleteEdges (G.incidenceSet x)).Adj

/-- Deleting the incidence set of the vertex `x` retains the same number of edges as in the induced
subgraph of the vertices `{x}ᶜ`. -/
theorem card_edgeFinset_induce_compl_singleton (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) :
    #(G.induce {x}ᶜ).edgeFinset = #(G.deleteIncidenceSet x).edgeFinset := by
  have h_notMem : x ∉ ({x}ᶜ : Set V) := Set.notMem_compl_iff.mpr (Set.mem_singleton x)
  simp_rw [edgeFinset, Set.toFinset_card,
    ← G.induce_deleteIncidenceSet_of_notMem h_notMem, ← Set.toFinset_card]
  apply card_edgeFinset_induce_of_support_subset
  trans G.support \ {x}
  · exact support_deleteIncidenceSet_subset G x
  · rw [Set.compl_eq_univ_diff]
    exact Set.diff_subset_diff_left (Set.subset_univ G.support)

/-- The finite edge set of `G.deleteIncidenceSet x` is the finite edge set of the simple graph `G`
set difference the finite incidence set of the vertex `x`. -/
theorem edgeFinset_deleteIncidenceSet_eq_sdiff (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) :
    (G.deleteIncidenceSet x).edgeFinset = G.edgeFinset \ G.incidenceFinset x := by
  apply Finset.coe_injective
  push_cast
  exact G.edgeSet_deleteIncidenceSet x

/-- Deleting the incident set of the vertex `x` deletes exactly `G.degree x` edges from the edge
set of the simple graph `G`. -/
theorem card_edgeFinset_deleteIncidenceSet (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) :
    #(G.deleteIncidenceSet x).edgeFinset = #G.edgeFinset - G.degree x := by
  simp_rw [← card_incidenceFinset_eq_degree, ← card_sdiff_of_subset (G.incidenceFinset_subset x),
    edgeFinset_deleteIncidenceSet_eq_sdiff]

/-- Deleting the incident set of the vertex `x` is equivalent to filtering the edges of the simple
graph `G` that do not contain `x`. -/
theorem edgeFinset_deleteIncidenceSet_eq_filter (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) :
    (G.deleteIncidenceSet x).edgeFinset = G.edgeFinset.filter (x ∉ ·) := by
  rw [edgeFinset_deleteIncidenceSet_eq_sdiff, sdiff_eq_filter]
  apply filter_congr
  intro _ h
  rw [incidenceFinset, Set.mem_toFinset, incidenceSet,
    Set.mem_setOf_eq, not_and, Classical.imp_iff_right_iff]
  left
  rwa [mem_edgeFinset] at h

/-- The support of `G.deleteIncidenceSet x` is at most `1` less than the support of the simple
graph `G`. -/
theorem card_support_deleteIncidenceSet
    (G : SimpleGraph V) [DecidableRel G.Adj] {x : V} (hx : x ∈ G.support) :
    card (G.deleteIncidenceSet x).support ≤ card G.support - 1 := by
  rw [← Set.singleton_subset_iff, ← Set.toFinset_subset_toFinset] at hx
  simp_rw [← Set.card_singleton x, ← Set.toFinset_card, ← card_sdiff_of_subset hx,
    ← Set.toFinset_diff]
  apply card_le_card
  rw [Set.toFinset_subset_toFinset]
  exact G.support_deleteIncidenceSet_subset x

end DeleteIncidenceSet

section DeleteFar

variable {𝕜 : Type*} [Ring 𝕜] [PartialOrder 𝕜]
  [Fintype G.edgeSet] {p : SimpleGraph V → Prop} {r r₁ r₂ : 𝕜}

/-- A graph is `r`-*delete-far* from a property `p` if we must delete at least `r` edges from it to
get a graph with the property `p`. -/
def DeleteFar (p : SimpleGraph V → Prop) (r : 𝕜) : Prop :=
  ∀ ⦃s⦄, s ⊆ G.edgeFinset → p (G.deleteEdges s) → r ≤ #s

variable {G}

theorem deleteFar_iff [Fintype (Sym2 V)] :
    G.DeleteFar p r ↔ ∀ ⦃H : SimpleGraph _⦄ [DecidableRel H.Adj],
      H ≤ G → p H → r ≤ #G.edgeFinset - #H.edgeFinset := by
  classical
  refine ⟨fun h H _ hHG hH ↦ ?_, fun h s hs hG ↦ ?_⟩
  · have := h (sdiff_subset (t := H.edgeFinset))
    simp only [deleteEdges_sdiff_eq_of_le hHG, edgeFinset_mono hHG, card_sdiff_of_subset,
      card_le_card, coe_sdiff, coe_edgeFinset, Nat.cast_sub] at this
    exact this hH
  · classical
    simpa [card_sdiff_of_subset hs, edgeFinset_deleteEdges, -Set.toFinset_card, Nat.cast_sub,
      card_le_card hs] using h (G.deleteEdges_le s) hG

alias ⟨DeleteFar.le_card_sub_card, _⟩ := deleteFar_iff

theorem DeleteFar.mono (h : G.DeleteFar p r₂) (hr : r₁ ≤ r₂) : G.DeleteFar p r₁ := fun _ hs hG =>
  hr.trans <| h hs hG

lemma DeleteFar.le_card_edgeFinset (h : G.DeleteFar p r) (hp : p ⊥) : r ≤ #G.edgeFinset :=
  h subset_rfl (by simpa)

end DeleteFar

end SimpleGraph
