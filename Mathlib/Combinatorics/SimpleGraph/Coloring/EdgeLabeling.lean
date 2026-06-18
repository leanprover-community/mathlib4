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
edge-coloring, but we reserve that terminology for labelings where incident edges cannot share a
label.
-/
def EdgeLabeling (G : SimpleGraph V) (K : Type*) :=
  G.edgeSet → K

instance [DecidableEq V] [Fintype G.edgeSet] [Fintype K] : Fintype (EdgeLabeling G K) :=
  inferInstanceAs <| Fintype (G.edgeSet → K)

instance [Finite G.edgeSet] [Finite K] : Finite (EdgeLabeling G K) :=
  Pi.finite

instance [Nonempty K] : Nonempty (EdgeLabeling G K) :=
  Pi.instNonempty

instance [Inhabited K] : Inhabited (EdgeLabeling G K) :=
  inferInstanceAs <| Inhabited (G.edgeSet → K)

instance [Subsingleton K] : Subsingleton (EdgeLabeling G K) :=
  Pi.instSubsingleton

instance [Nonempty G.edgeSet] [Nontrivial K] : Nontrivial (EdgeLabeling G K) :=
  Function.nontrivial

instance [Unique K] : Unique (EdgeLabeling G K) :=
  inferInstanceAs <| Unique (G.edgeSet → K)

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
Convenience function to get the color of the edge `x ~ y` in the coloring of the complete graph
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

/-- Compose an edge-labeling with a function on the color set. -/
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
    refine Sym2.hrec f (fun a b ↦ ?_) e
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
we don't know how to color `x ~ y` in the case `f x = f y`.
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

namespace EdgeLabeling

/-- The predicate `C.MonochromaticBetween X Y k` says every edge between `X` and `Y` is labelled
`k` by the labelling `C`. -/
def MonochromaticBetween (C : EdgeLabeling G K) (X Y : Set V) (k : K) : Prop :=
  ∀ ⦃x⦄, x ∈ X → ∀ ⦃y⦄, y ∈ Y → (h : G.Adj x y) → C.get x y h = k

/-- `C.MonochromaticOf X k` says that every edge in `X` is labelled `k` by the labelling `C`. -/
def MonochromaticOf (C : EdgeLabeling G K) (X : Set V) (k : K) : Prop :=
  MonochromaticBetween C X X k

variable {W X Y Z : Set V} {k : K} {C : EdgeLabeling G K}

theorem monochromaticOf_iff_pairwise :
    C.MonochromaticOf X k ↔ X.Pairwise fun x y ↦ ∀ h : G.Adj x y, C.get x y h = k := by
  grind [MonochromaticOf, MonochromaticBetween, Set.Pairwise, Adj.ne]

lemma _root_.SimpleGraph.TopEdgeLabeling.monochromaticOf_iff_ne_of_adj {C : TopEdgeLabeling V K} :
    C.MonochromaticOf X k ↔ ∀ ⦃x⦄, x ∈ X → ∀ ⦃y⦄, y ∈ X → (h : x ≠ y) → C.get x y h = k := by
  simp_rw [MonochromaticOf, MonochromaticBetween, top_adj]

namespace MonochromaticBetween

protected theorem symm (hXY : C.MonochromaticBetween X Y k) : C.MonochromaticBetween Y X k := by
  intro y hy x hx h
  rw [get_comm _ _ h]
  exact hXY hx hy _

protected theorem comm : C.MonochromaticBetween Y X k ↔ C.MonochromaticBetween X Y k :=
  ⟨.symm, .symm⟩

@[simp]
theorem empty_left : C.MonochromaticBetween ∅ Y k := by
  simp [MonochromaticBetween]

@[simp]
theorem empty_right : C.MonochromaticBetween X ∅ k := by
  simp [MonochromaticBetween]

theorem singleton_left {x : V} :
    C.MonochromaticBetween {x} Y k ↔ ∀ ⦃y⦄, y ∈ Y → (h : G.Adj x y) → C.get x y h = k := by
  simp [MonochromaticBetween]

theorem singleton_right {y : V} :
    C.MonochromaticBetween X {y} k ↔ ∀ ⦃x⦄, x ∈ X → (h : G.Adj x y) → C.get x y h = k := by
  simp [MonochromaticBetween]

theorem subsingleton_colours [Subsingleton K] : C.MonochromaticBetween X Y k :=
  fun _ _ _ _ _ ↦ Subsingleton.elim _ _

theorem union_left : C.MonochromaticBetween (X ∪ Y) Z k ↔
    C.MonochromaticBetween X Z k ∧ C.MonochromaticBetween Y Z k := by
  grind [MonochromaticBetween]

theorem union_right : C.MonochromaticBetween X (Y ∪ Z) k ↔
    C.MonochromaticBetween X Y k ∧ C.MonochromaticBetween X Z k := by
  grind [MonochromaticBetween]

protected theorem self : C.MonochromaticBetween X X k ↔ C.MonochromaticOf X k :=
  .rfl

protected theorem subset (hWX : C.MonochromaticBetween W X k) (hYW : Y ⊆ W) (hZX : Z ⊆ X) :
    C.MonochromaticBetween Y Z k :=
  fun _ hx _ hy ↦ hWX (hYW hx) (hZX hy)

protected theorem subset_left (hYZ : C.MonochromaticBetween Y Z k) (hXY : X ⊆ Y) :
    C.MonochromaticBetween X Z k :=
  hYZ.subset hXY (Set.Subset.refl Z)

protected theorem subset_right (hXZ : C.MonochromaticBetween X Z k) (hXY : Y ⊆ Z) :
    C.MonochromaticBetween X Y k :=
  hXZ.subset (Set.Subset.refl X) hXY

protected theorem image {C : EdgeLabeling G' K} {f : G ↪g G'}
    (hXY : (C.pullback f.toHom).MonochromaticBetween X Y k) :
    C.MonochromaticBetween (f '' X) (f '' Y) k := by
  simpa [MonochromaticBetween]

theorem compRight (h : C.MonochromaticBetween X Y k) (e : K → K') :
    (C.compRight e).MonochromaticBetween X Y (e k) := by
  intro x hx y hy h'
  rw [compRight_get, h hx hy h']

protected theorem injective (e : K → K') (he : Function.Injective e) :
    (C.compRight e).MonochromaticBetween X Y (e k) ↔ C.MonochromaticBetween X Y k := by
  simp_rw [EdgeLabeling.compRight, MonochromaticBetween, get_eq, Function.comp_apply, he.eq_iff]

end MonochromaticBetween

namespace MonochromaticOf

theorem subsingleton (hm : X.Subsingleton) : C.MonochromaticOf X k :=
  fun _ hx _ hy h ↦ (h.ne (hm hx hy)).elim

@[simp]
protected theorem empty : C.MonochromaticOf ∅ k :=
  .subsingleton Set.subsingleton_empty

@[simp]
protected theorem singleton {x : V} : C.MonochromaticOf {x} k :=
  .subsingleton Set.subsingleton_singleton

theorem subsingleton_colours [Subsingleton K] : C.MonochromaticOf X k :=
  MonochromaticBetween.subsingleton_colours

theorem compRight (h : C.MonochromaticOf X k) (e : K → K') :
    (C.compRight e).MonochromaticOf X (e k) :=
  MonochromaticBetween.compRight h e

protected theorem injective (e : K → K') (he : Function.Injective e) :
    (C.compRight e).MonochromaticOf X (e k) ↔ C.MonochromaticOf X k :=
  MonochromaticBetween.injective e he

theorem subset (hY : C.MonochromaticOf Y k) (hXY : X ⊆ Y) : C.MonochromaticOf X k :=
  MonochromaticBetween.subset hY hXY hXY

theorem image {C : EdgeLabeling G' K} {f : G ↪g G'} (h : (C.pullback f.toHom).MonochromaticOf X k) :
    C.MonochromaticOf (f '' X) k :=
  MonochromaticBetween.image h

protected theorem union : C.MonochromaticOf (X ∪ Y) k ↔
    C.MonochromaticOf X k ∧ C.MonochromaticOf Y k ∧ C.MonochromaticBetween X Y k := by
  grind [MonochromaticOf, MonochromaticBetween.union_left, MonochromaticBetween.comm]

protected theorem insert {x : V} :
    C.MonochromaticOf (insert x X) k ↔ C.MonochromaticOf X k ∧ C.MonochromaticBetween X {x} k := by
  simp [← Set.union_singleton, MonochromaticOf.union]

theorem image_top {C : TopEdgeLabeling V' K} {f : V ↪ V'}
    (h : (C.pullback f).MonochromaticOf X k) : C.MonochromaticOf (f '' X) k := by
  simpa [TopEdgeLabeling.monochromaticOf_iff_ne_of_adj]

theorem map_top {C : TopEdgeLabeling V' K} {f : V ↪ V'} {m : Finset V}
    (h : (C.pullback f).MonochromaticOf m k) : C.MonochromaticOf (m.map f) k := by
  rw [coe_map]
  exact h.image_top

end MonochromaticOf

end EdgeLabeling

end SimpleGraph
