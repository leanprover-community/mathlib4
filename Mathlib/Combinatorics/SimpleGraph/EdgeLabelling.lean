/-
Copyright (c) 2023 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Olivia Röhrig
-/
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Finset.Pairwise

/-!
# Edge labellings

This module defines labellings of the edges of a graph.

## Main definitions

- `SimpleGraph.EdgeLabelling`: An assignment of a label from a given type to each edge of the graph.

- `SimpleGraph.EdgeLabelling.labelGraph`: the graph consisting of all edges with a given label.
-/

open Finset
open Fintype (card)

namespace SimpleGraph

variable {V V' : Type*} {G : SimpleGraph V} {G' : SimpleGraph V'} {K K' : Type*}

/-- An edge labelling of a simple graph `G` with labels in type `K`. Sometimes this is called an
edge-colouring, but we reserve that terminology for labellings where incident edges cannot share a
label.
-/
def EdgeLabelling (G : SimpleGraph V) (K : Type*) :=
  G.edgeSet → K

instance [DecidableEq V] [Fintype G.edgeSet] [Fintype K] : Fintype (EdgeLabelling G K) :=
  Pi.instFintype

instance [Nonempty K] : Nonempty (EdgeLabelling G K) :=
  Pi.instNonempty

instance [Inhabited K] : Inhabited (EdgeLabelling G K) :=
  Pi.instInhabited

instance [Subsingleton K] : Subsingleton (EdgeLabelling G K) :=
  Pi.instSubsingleton

instance [Unique K] : Unique (EdgeLabelling G K) :=
  Pi.unique

/--
An edge labelling of the complete graph on `V` with labels in type `K`. Sometimes this is called an
edge-colouring, but we reserve that terminology for labellings where incident edges cannot share a
label.
-/
abbrev TopEdgeLabelling (V : Type*) (K : Type*) :=
  EdgeLabelling (⊤ : SimpleGraph V) K

theorem card_EdgeLabelling [DecidableEq V] [Fintype V] [Fintype K] :
    card (TopEdgeLabelling V K) = card K ^ (card V).choose 2 :=
  Fintype.card_fun.trans (by rw [card_top_edgeSet])

namespace EdgeLabelling

/--
Convenience function to get the colour of the edge `x ~ y` in the colouring of the complete graph
on `V`.
-/
def get (C : EdgeLabelling G K) (x y : V) (h : G.Adj x y) : K :=
  C ⟨s(x, y), h⟩

variable {C : EdgeLabelling G K}

theorem get_swap (x y : V) (h : G.Adj x y) : C.get y x h.symm = C.get x y h := by
  simp only [EdgeLabelling.get, Sym2.eq_swap]

@[ext]
theorem ext_get {C' : EdgeLabelling G K}
    (h : ∀ x y, (h : G.Adj x y) → C.get x y h = C'.get x y h) : C = C' := by
  refine funext fun ⟨e, he⟩ => ?_
  induction e using Sym2.inductionOn
  exact h _ _ he

/-- Compose an edge-labelling with a function on the colour set. -/
def compRight (C : EdgeLabelling G K) (f : K → K') : EdgeLabelling G K' :=
  f ∘ C

/-- Compose an edge-labelling with a graph embedding. -/
def pullback (C : EdgeLabelling G K) (f : G' ↪g G) : EdgeLabelling G' K :=
  C ∘ f.mapEdgeSet

@[simp]
theorem pullback_apply {f : G' ↪g G} e :
    C.pullback f e = C (f.mapEdgeSet e) :=
  rfl

@[simp]
theorem pullback_get {f : G' ↪g G} (x y) (h : G'.Adj x y) :
    (C.pullback f).get x y h = C.get (f x) (f y) (by simpa) :=
  rfl

@[simp]
theorem compRight_apply (f : K → K') (e) : C.compRight f e = f (C e) :=
  rfl

@[simp]
theorem compRight_get (f : K → K') (x y) (h : G.Adj x y) :
    (C.compRight f).get x y h = f (C.get x y h) :=
  rfl

attribute [scoped instance] Sym2.Rel.setoid in
/-- Construct an edge labelling from a symmetric function taking values everywhere except the
diagonal.
-/
def mk (f : ∀ x y : V, G.Adj x y → K)
    (f_symm : ∀ (x y : V) (H : G.Adj x y), f y x H.symm = f x y H) : EdgeLabelling G K :=
  fun ⟨e, he⟩ => by
    revert he
    refine Quotient.hrecOn e (fun xy => f xy.1 xy.2) ?_
    rintro ⟨a, b⟩ ⟨c, d⟩ ⟨⟩
    · rfl
    refine Function.hfunext ?_ ?_
    · ext; simp only [adj_comm]
    · intro h₁ h₂ _
      exact heq_of_eq (f_symm _ _ _)

theorem mk_get (f : ∀ x y : V, G.Adj x y → K) (f_symm) (x y : V) (h : G.Adj x y) :
    (EdgeLabelling.mk f f_symm).get x y h = f x y h :=
  rfl

/--
Given an edge labelling and a choice of label `k`, construct the graph corresponding to the edges
labelled `k`.
-/
def labelGraph (C : EdgeLabelling G K) (k : K) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet {e | ∃ h : e ∈ G.edgeSet, C ⟨e, h⟩ = k}

theorem labelGraph_adj {C : EdgeLabelling G K} {k : K} (x y : V) :
    (C.labelGraph k).Adj x y ↔ ∃ H : G.Adj x y, C ⟨s(x, y), H⟩ = k := by
  rw [EdgeLabelling.labelGraph]
  simp only [mem_edgeSet, fromEdgeSet_adj, Set.mem_setOf_eq, Ne.eq_def]
  apply and_iff_left_of_imp _
  rintro ⟨h, -⟩
  exact h.ne

instance [DecidableRel G.Adj] [DecidableEq K] (k : K) {C : EdgeLabelling G K} :
    DecidableRel (C.labelGraph k).Adj := fun _ _ =>
  decidable_of_iff' _ (EdgeLabelling.labelGraph_adj _ _)

theorem labelGraph_le (C : EdgeLabelling G K) {k : K} : C.labelGraph k ≤ G := by
  intro x y
  rw [EdgeLabelling.labelGraph_adj]
  rintro ⟨h, -⟩
  exact h

theorem pairwiseDisjoint {C : EdgeLabelling G K} :
    Set.PairwiseDisjoint (Set.univ : Set K) C.labelGraph := by
  intro k₁ hk₁ k₂ _ h
  rw [Function.onFun, SimpleGraph.disjoint_left]
  simp only [labelGraph_adj, not_exists, forall_exists_index]
  rintro x y h rfl _
  exact h

theorem iSup_labelGraph (C : EdgeLabelling G K) : (⨆ k : K, C.labelGraph k) = G := by
  ext x y
  simp only [iSup_adj, EdgeLabelling.labelGraph_adj]
  constructor
  · rintro ⟨k, h, rfl⟩
    exact h
  intro h
  exact ⟨_, h, rfl⟩

end EdgeLabelling

namespace TopEdgeLabelling

/-- Compose an edge-labelling, by an injection into the vertex type. This must be an injection, else
we don't know how to colour `x ~ y` in the case `f x = f y`.
-/
abbrev pullback (C : TopEdgeLabelling V K) (f : V' ↪ V) : TopEdgeLabelling V' K :=
  EdgeLabelling.pullback C ⟨f, by simp⟩

@[simp]
theorem labelGraph_adj {C : TopEdgeLabelling V K} {k : K} (x y : V) :
    (C.labelGraph k).Adj x y ↔ ∃ H : x ≠ y, C.get x y H = k := by
  rw [EdgeLabelling.labelGraph_adj]
  simp
  rfl

end TopEdgeLabelling

/--
From a simple graph on `V`, construct the edge labelling on the complete graph of `V` given where
edges are labelled `1` and non-edges are labelled `0`.
-/
def toTopEdgeLabelling (G : SimpleGraph V) [DecidableRel G.Adj] : TopEdgeLabelling V (Fin 2) :=
  EdgeLabelling.mk (fun x y _ => if G.Adj x y then 1 else 0) fun x y _ => by
    simp only [G.adj_comm]

@[simp]
theorem toTopEdgeLabelling_get {G : SimpleGraph V} [DecidableRel G.Adj] {x y : V} (H : x ≠ y) :
    G.toTopEdgeLabelling.get x y H = if G.Adj x y then 1 else 0 :=
  rfl

theorem toTopEdgeLabelling_labelGraph (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.toTopEdgeLabelling.labelGraph 1 = G := by ext x y; simpa [imp_false] using G.ne_of_adj

theorem toTopEdgeLabelling_labelGraph_compl (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.toTopEdgeLabelling.labelGraph 0 = Gᶜ := by ext x y; simp [imp_false]

theorem TopEdgeLabelling.labelGraph_toTopEdgeLabelling [DecidableEq V]
    (C : TopEdgeLabelling V (Fin 2)) : (C.labelGraph 1).toTopEdgeLabelling = C := by
  refine EdgeLabelling.ext_get ?_
  intro x y h
  simp only [Ne.eq_def, toTopEdgeLabelling_get, TopEdgeLabelling.labelGraph_adj]
  split_ifs with h_1
  · rw [← h_1.choose_spec]
  have : ∀ {x : Fin 2},  x ≠ 1 → x = 0 := by decide
  exact (this ((not_exists.mp h_1) h)).symm

end SimpleGraph
