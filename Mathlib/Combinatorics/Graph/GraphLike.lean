/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon, Laura Monk, Freddie Nash
-/
module

public import Mathlib.Combinatorics.GraphLike.Basic
public import Mathlib.Combinatorics.Graph.Basic

/-!
We define a `Dart` type as a directed edge, and a `GraphLike` instance for `Graph`.
-/

public section

variable {V E : Type*} {G : Graph V E}

namespace Graph

/-- `Graph.Dart` is a type for darts or length 1 walks of `Graph`. Every edge of a graph is composed
  of two darts: for loops, there are `fwd` and `bwd` darts, and for non-loops, there are two `dir`
  darts. -/
inductive IncidenceType (α β : Type*) : Type _ where
  | dir : β → ∀ (u v : α), u ≠ v → IncidenceType α β
  | fwd : β → α → IncidenceType α β
  | bwd : β → α → IncidenceType α β

open HyperGraphLike

@[expose]
def IncidenceType.edge (d : IncidenceType V E) : E :=
  match d with
  | .dir e _ _ _ => e
  | .fwd e _ => e
  | .bwd e _ => e

@[expose]
def IncidenceType.source (d : IncidenceType V E) : V :=
  match d with
  | .dir _ u _ _ => u
  | .fwd _ v => v
  | .bwd _ v => v

@[expose]
def IncidenceType.target (d : IncidenceType V E) : V :=
  match d with
  | .dir _ _ v _ => v
  | .fwd _ v => v
  | .bwd _ v => v

lemma IncidenceType.dir_of_ne {d : IncidenceType V E} (hne : d.source ≠ d.target) :
    d = IncidenceType.dir d.edge d.source d.target hne := by
  cases d <;> grind [source, target, edge]

lemma IncidenceType.fwd_or_bwd_of_eq {d : IncidenceType V E} (heq : d.source = d.target) :
    d = IncidenceType.fwd d.edge d.source ∨ d = IncidenceType.bwd d.edge d.target := by
  cases d <;> grind [source, target, edge]

def IsLink.inc1 [DecidableEq V] {e u v} (_ : G.IsLink e u v) :=
    if h : u = v then IncidenceType.fwd e u else IncidenceType.dir e u v h

def IsLink.inc2 [DecidableEq V] {e u v} (_ : G.IsLink e u v) :=
    if h : u = v then IncidenceType.bwd e u else IncidenceType.dir e v u (Ne.symm h)

@[simp, grind →]
lemma IsLink.inc1_edge [DecidableEq V] {e u v} (h : G.IsLink e u v) :
    h.inc1.edge = e := by
  by_cases huv : u = v <;> simp [inc1, huv, IncidenceType.edge]

@[simp, grind →]
lemma IsLink.inc2_edge [DecidableEq V] {e u v} (h : G.IsLink e u v) :
    h.inc2.edge = e := by
  by_cases huv : u = v <;> simp [inc2, huv, IncidenceType.edge]

@[simp, grind →]
lemma IsLink.inc1_source [DecidableEq V] {e u v} (h : G.IsLink e u v) :
    h.inc1.source = u := by
  by_cases huv : u = v <;> simp [inc1, huv, IncidenceType.source]

@[simp, grind →]
lemma IsLink.inc2_source [DecidableEq V] {e u v} (h : G.IsLink e u v) :
    h.inc2.source = v := by
  by_cases huv : u = v <;> simp [inc2, huv, IncidenceType.source]

@[simp, grind →]
lemma IsLink.inc1_target [DecidableEq V] {e u v} (h : G.IsLink e u v) :
    h.inc1.target = v := by
  by_cases huv : u = v <;> simp [inc1, huv, IncidenceType.target]

@[simp, grind →]
lemma IsLink.inc2_target [DecidableEq V] {e u v} (h : G.IsLink e u v) :
    h.inc2.target = u := by
  by_cases huv : u = v <;> simp [inc2, huv, IncidenceType.target]

@[simp, grind →]
lemma IsLink.inc1_ne_inc2 [DecidableEq V] {e u v} (h : G.IsLink e u v) :
    h.inc1 ≠ h.inc2 := by
  by_cases huv : u = v <;> simp [inc1, inc2, huv]

lemma isLink_iff_exists_incidenceType (e u v) : G.IsLink e u v ↔ ∃ i j : IncidenceType V E, i ≠ j ∧
    G.IsLink i.edge i.source i.target ∧ G.IsLink j.edge j.source j.target ∧
    (G.IsLink i.edge i.source i.target ∧ i.source = u ∧ i.edge = e) ∧
    (G.IsLink j.edge j.source j.target ∧ j.source = v ∧ j.edge = e) := by
    classical
    refine ⟨fun h => ?_, fun ⟨i, j, hij, hi, hj, hi', hj'⟩ => ?_⟩
    · use h.inc1, h.inc2, h.inc1_ne_inc2, ?_, ?_, ⟨?_, h.inc1_source, h.inc1_edge⟩, ?_,
        h.inc2_source, h.inc2_edge <;> simp [h, h.symm]
    obtain ⟨-, rfl, rfl⟩ := hi'
    obtain ⟨-, rfl, he⟩ := hj'
    have := hi.eq_and_eq_or_eq_and_eq (he ▸ hj)
    obtain heq | hne := eq_or_ne i.source i.target
    · grind
    obtain ⟨hs, ht⟩ | ⟨hs, ht⟩ := this.symm
    · grind
    have hjne : j.source ≠ j.target := by grind
    grind [IncidenceType.dir_of_ne hne, IncidenceType.dir_of_ne hjne]

@[simps (attr := grind =) -isSimp]
instance : HyperGraphLike V (IncidenceType V E) E (Graph V E) where
  verts G := V(G)
  edges G := E(G)
  IsIncident G i e v := G.IsLink i.edge i.source i.target ∧ i.source = v ∧ i.edge = e
  IsSource G i := G.IsLink i.edge i.source i.target
  IsTarget G i := G.IsLink i.edge i.source i.target
  vert_mem_of_isIncident G i e v hi := by grind
  edge_mem_of_isIncident G i e v hi := by grind [IsLink.edge_mem]
  eq_and_eq_of_isIncident_of_isIncident _ _ _ _ _ _ := by grind
  isIncident_iff G i := by grind
  IsLink G e u v := G.IsLink e u v
  isLink_def G e u v := isLink_iff_exists_incidenceType e u v
  Adj G u v := G.Adj u v
  adj_def G u v := exists_congr fun e ↦ isLink_iff_exists_incidenceType e u v

lemma edgeIncidents_eq_fwd_bwd_of_isLink_loop {e : E} {x : V} (h : G.IsLink e x x) :
    edgeIncidents G e = {IncidenceType.fwd e x, IncidenceType.bwd e x} := by
  ext i
  rcases i with ⟨e₀, u, v, huv⟩ | ⟨e₀, v⟩ | ⟨e₀, v⟩ <;>
  simp only [mem_edgeIncidents_iff, IsIncident] <;>
  grind [IsLink.eq_and_eq_or_eq_and_eq, IncidenceType.edge, IncidenceType.source,
    IncidenceType.target]

lemma edgeIncidents_eq_dir_of_isLink_nonloop {e : E} {x y : V} (h : G.IsLink e x y) (hxy : x ≠ y) :
    edgeIncidents G e = {IncidenceType.dir e x y hxy, IncidenceType.dir e y x (Ne.symm hxy)} := by
  ext i
  rcases i with ⟨e₀, u, v, huv⟩ | ⟨e₀, v⟩ | ⟨e₀, v⟩ <;>
  simp only [mem_edgeIncidents_iff, IsIncident] <;>
  grind [IsLink.eq_and_eq_or_eq_and_eq, IncidenceType.edge, IncidenceType.source,
    IncidenceType.target, IsLink.symm]

lemma order_eq_two_of_isLink {e : E} {x y : V} (h : G.IsLink e x y) : order G e = 2 := by
  rw [order]
  obtain rfl | hne := eq_or_ne x y
  · rw [edgeIncidents_eq_fwd_bwd_of_isLink_loop h]
    exact Set.encard_pair (by grind)
  rw [edgeIncidents_eq_dir_of_isLink_nonloop h hne]
  exact Set.encard_pair (by grind)

instance : GraphLike V (IncidenceType V E) E (Graph V E) where
  order_eq_two G e he := by
    obtain ⟨x, y, h⟩ := exists_isLink_of_mem_edgeSet he
    exact order_eq_two_of_isLink h
  exists_isSource_of_mem_edgeSet G e he := by
    obtain ⟨x, y, h⟩ := exists_isLink_of_mem_edgeSet he
    classical
    exact ⟨h.inc1, ⟨x, by simpa, by simp⟩, by simpa [IsSource]⟩
  exists_isTarget_of_mem_edgeSet G e he := by
    obtain ⟨x, y, h⟩ := exists_isLink_of_mem_edgeSet he
    classical
    exact ⟨h.inc2, ⟨y, by simp [h.symm], by simp⟩, by simp [IsTarget, h.symm]⟩

instance : undirected V (IncidenceType V E) E (Graph V E) where
  isSource_iff G i := by simp [IsSource, IsTarget]

end Graph
