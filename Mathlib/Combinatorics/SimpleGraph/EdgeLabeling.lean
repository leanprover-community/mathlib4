/-
Copyright (c) 2023 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Olivia Röhrig
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Fintype.BigOperators

/-!
# Edge labelings

This module defines labelings of the edges of a graph.

## Main definitions

- `SimpleGraph.EdgeLabeling`: An assignment of a label from a given type to each edge of the graph.

- `SimpleGraph.EdgeLabeling.labelGraph`: the graph consisting of all edges with a given label.
-/

@[expose] public section

open Finset
open Fintype (card)

namespace SimpleGraph

variable {V V' : Type*} {G : SimpleGraph V} {G' : SimpleGraph V'} {K K' : Type*}

/-- An edge labeling of a simple graph `G` with labels in type `K`. Sometimes this is called an
edge-colouring, but we reserve that terminology for labelings where incident edges cannot share a
label.
-/
def EdgeLabeling (G : SimpleGraph V) (K : Type*) :=
  G.edgeSet → K

instance [DecidableEq V] [Fintype G.edgeSet] [Fintype K] : Fintype (EdgeLabeling G K) :=
  Pi.instFintype

instance [Finite G.edgeSet] [Finite K] : Finite (EdgeLabeling G K) :=
  Pi.finite

instance [Nonempty K] : Nonempty (EdgeLabeling G K) :=
  Pi.instNonempty

instance [Inhabited K] : Inhabited (EdgeLabeling G K) :=
  Pi.instInhabited

instance [Subsingleton K] : Subsingleton (EdgeLabeling G K) :=
  Pi.instSubsingleton

instance [Nonempty G.edgeSet] [Nontrivial K] : Nontrivial (EdgeLabeling G K) :=
  Function.nontrivial

instance [Unique K] : Unique (EdgeLabeling G K) :=
  Pi.unique

/--
An edge labeling of the complete graph on `V` with labels in type `K`.
-/
abbrev TopEdgeLabeling (V K : Type*) :=
  EdgeLabeling (⊤ : SimpleGraph V) K

theorem card_topEdgeLabeling [DecidableEq V] [Fintype V] [Fintype K] :
    card (TopEdgeLabeling V K) = card K ^ (card V).choose 2 :=
  Fintype.card_fun.trans (by rw [← edgeFinset_card, card_edgeFinset_top_eq_card_choose_two])

namespace EdgeLabeling

/--
Convenience function to get the colour of the edge `x ~ y` in the colouring of the complete graph
on `V`.
-/
def get (C : EdgeLabeling G K) (x y : V) (h : G.Adj x y) : K :=
  C ⟨s(x, y), h⟩

lemma get_eq (C : EdgeLabeling G K) (x y : V) (h : G.Adj x y) : C.get x y h = C ⟨s(x, y), h⟩ :=
  rfl

variable {C : EdgeLabeling G K}

theorem get_comm (x y : V) (h) : C.get y x h = C.get x y h.symm := by
  simp [EdgeLabeling.get, Sym2.eq_swap]

@[ext]
theorem ext_get {C' : EdgeLabeling G K}
    (h : ∀ x y, (h : G.Adj x y) → C.get x y h = C'.get x y h) : C = C' := by
  funext ⟨e, he⟩
  induction e using Sym2.inductionOn
  exact h _ _ he

/-- Compose an edge-labeling with a function on the colour set. -/
def compRight (C : EdgeLabeling G K) (f : K → K') : EdgeLabeling G K' :=
  f ∘ C

/-- Compose an edge-labeling with a graph embedding. -/
def pullback (C : EdgeLabeling G K) (f : G' →g G) : EdgeLabeling G' K :=
  C ∘ f.mapEdgeSet

@[simp]
theorem pullback_apply {f : G' →g G} e : C.pullback f e = C (f.mapEdgeSet e) :=
  rfl

@[simp]
theorem get_pullback {f : G' ↪g G} (x y) (h : G'.Adj x y) :
    (C.pullback f).get x y h = C.get (f x) (f y) (by simpa) :=
  rfl

@[simp]
theorem compRight_apply (f : K → K') (e) : C.compRight f e = f (C e) :=
  rfl

@[simp]
theorem compRight_get (f : K → K') (x y) (h : G.Adj x y) :
    (C.compRight f).get x y h = f (C.get x y h) :=
  rfl

/-- Construct an edge labeling from a symmetric function on adjacent vertices. -/
def mk (f : ∀ x y : V, G.Adj x y → K)
    (f_symm : ∀ (x y : V) (H : G.Adj x y), f y x H.symm = f x y H) : EdgeLabeling G K
  | ⟨e, he⟩ => by
    revert he
    refine Sym2.hrec (fun xy ↦ f xy.1 xy.2) (fun a b ↦ ?_) e
    apply Function.hfunext (by simp [adj_comm])
    grind

theorem get_mk (f : ∀ x y : V, G.Adj x y → K) (f_symm) (x y : V) (h : G.Adj x y) :
    (mk f f_symm).get x y h = f x y h :=
  rfl

/--
Given an edge labeling and a choice of label `k`, construct the graph corresponding to the edges
labeled `k`.
-/
def labelGraph (C : EdgeLabeling G K) (k : K) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet {e | ∃ h : e ∈ G.edgeSet, C ⟨e, h⟩ = k}

theorem labelGraph_adj {C : EdgeLabeling G K} {k : K} (x y : V) :
    (C.labelGraph k).Adj x y ↔ ∃ H : G.Adj x y, C ⟨s(x, y), H⟩ = k := by
  rw [EdgeLabeling.labelGraph]
  simp only [mem_edgeSet, fromEdgeSet_adj, Set.mem_setOf_eq, Ne.eq_def]
  grind [Adj.ne]

instance [DecidableRel G.Adj] [DecidableEq K] (k : K) {C : EdgeLabeling G K} :
    DecidableRel (C.labelGraph k).Adj := fun _ _ =>
  decidable_of_iff' _ (EdgeLabeling.labelGraph_adj _ _)

theorem labelGraph_le (C : EdgeLabeling G K) {k : K} : C.labelGraph k ≤ G := by
  intro x y
  grind [labelGraph_adj]

theorem pairwise_disjoint_labelGraph {C : EdgeLabeling G K} :
    Pairwise fun k l ↦ Disjoint (C.labelGraph k) (C.labelGraph l) := by
  intro _ _ h
  rw [disjoint_left]
  grind [labelGraph_adj]

theorem pairwiseDisjoint_univ_labelGraph {C : EdgeLabeling G K} :
    Set.PairwiseDisjoint (@Set.univ K) C.labelGraph := by
  intro _ _ _ _ h
  exact pairwise_disjoint_labelGraph h

theorem iSup_labelGraph (C : EdgeLabeling G K) : ⨆ k : K, C.labelGraph k = G := by
  ext x y
  simp only [iSup_adj, EdgeLabeling.labelGraph_adj]
  grind

end EdgeLabeling

namespace TopEdgeLabeling

/-- Compose an edge-labeling, by an injection into the vertex type. This must be an injection, else
we don't know how to colour `x ~ y` in the case `f x = f y`.
-/
abbrev pullback (C : TopEdgeLabeling V K) (f : V' ↪ V) : TopEdgeLabeling V' K :=
  EdgeLabeling.pullback C ⟨f, by simp⟩

@[simp]
theorem labelGraph_adj {C : TopEdgeLabeling V K} {k : K} (x y : V) :
    (C.labelGraph k).Adj x y ↔ ∃ H : x ≠ y, C.get x y H = k := by
  simp [EdgeLabeling.labelGraph_adj, EdgeLabeling.get_eq]

end TopEdgeLabeling

/--
From a simple graph on `V`, construct the edge labeling on the complete graph of `V` given where
edges are labeled `1` and non-edges are labeled `0`.
-/
def toTopEdgeLabeling (G : SimpleGraph V) [DecidableRel G.Adj] : TopEdgeLabeling V (Fin 2) :=
  EdgeLabeling.mk (fun x y _ => if G.Adj x y then 1 else 0) (by simp [G.adj_comm])

@[simp]
theorem toTopEdgeLabeling_get {G : SimpleGraph V} [DecidableRel G.Adj] {x y : V} (H : x ≠ y) :
    G.toTopEdgeLabeling.get x y H = if G.Adj x y then 1 else 0 :=
  rfl

@[simp]
theorem toTopEdgeLabeling_labelGraph (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.toTopEdgeLabeling.labelGraph 1 = G := by ext x y; simpa [imp_false] using G.ne_of_adj

@[simp]
theorem toTopEdgeLabeling_labelGraph_compl (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.toTopEdgeLabeling.labelGraph 0 = Gᶜ := by ext x y; simp [imp_false]

theorem TopEdgeLabeling.labelGraph_toTopEdgeLabeling [DecidableEq V]
    (C : TopEdgeLabeling V (Fin 2)) : (C.labelGraph 1).toTopEdgeLabeling = C := by
  refine EdgeLabeling.ext_get ?_
  grind [toTopEdgeLabeling_get, TopEdgeLabeling.labelGraph_adj, Adj.ne]

end SimpleGraph
