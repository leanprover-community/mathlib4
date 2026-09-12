/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon, Laura Monk, Freddie Nash
-/
module

public import Mathlib.Combinatorics.GraphLike.Basic
public import Mathlib.Combinatorics.Graph.Basic

/-!
# Graphs as graph-like structures

This file defines `Incidence` and uses it to show that `Graph` is `HyperGraphLike`,
`GraphLike`, and `Undirected`, with incidence identifiers of type `Incidence V E` (directed
darts: `dir` for non-loops, and `fwd`/`bwd` for loops).
-/

public section

variable {V E : Type*} {G : Graph V E} {e f : E} {u v x y : V}

namespace Graph

/-- `Graph.Dart` is a type for darts or length 1 walks of `Graph`. Every edge of a graph is composed
  of two darts: for loops, there are `fwd` and `bwd` darts, and for non-loops, there are two `dir`
  darts. -/
inductive Incidence (α β : Type*) : Type _ where
  | dir : β → ∀ (u v : α), u ≠ v → Incidence α β
  | fwd : β → α → Incidence α β
  | bwd : β → α → Incidence α β

open HyperGraphLike Incidence

variable {d : Incidence V E}

/-- The edge of a `Incidence`. -/
@[expose]
def Incidence.edge (d : Incidence V E) : E :=
  match d with
  | .dir e _ _ _ => e
  | .fwd e _ => e
  | .bwd e _ => e

/-- The source of a `Incidence`. -/
@[expose]
def Incidence.source (d : Incidence V E) : V :=
  match d with
  | .dir _ u _ _ => u
  | .fwd _ v => v
  | .bwd _ v => v

/-- The target of a `Incidence`. -/
@[expose]
def Incidence.target (d : Incidence V E) : V :=
  match d with
  | .dir _ _ v _ => v
  | .fwd _ v => v
  | .bwd _ v => v

lemma Incidence.dir_of_ne (hne : d.source ≠ d.target) :
    d = dir d.edge d.source d.target hne := by
  cases d <;> grind [source, target, edge]

lemma Incidence.fwd_or_bwd_of_eq (heq : d.source = d.target) :
    d = fwd d.edge d.source ∨ d = bwd d.edge d.target := by
  cases d <;> grind [source, target, edge]

section firstSecondIncidence

variable [DecidableEq V] (e : E) (u v : V)

/-- The first incidence of a link. -/
def firstIncidence := if h : u = v then fwd e u else dir e u v h

/-- The second incidence of a link. -/
def secondIncidence := if h : u = v then bwd e u else dir e v u (Ne.symm h)

@[simp, grind =]
lemma firstIncidence_edge : (firstIncidence e u v).edge = e := by
  by_cases huv : u = v <;> simp [firstIncidence, huv, edge]

@[simp, grind =]
lemma secondIncidence_edge : (secondIncidence e u v).edge = e := by
  by_cases huv : u = v <;> simp [secondIncidence, huv, edge]

@[simp, grind =]
lemma firstIncidence_source : (firstIncidence e u v).source = u := by
  by_cases huv : u = v <;> simp [firstIncidence, huv, source]

@[simp, grind =]
lemma secondIncidence_source : (secondIncidence e u v).source = v := by
  by_cases huv : u = v <;> simp [secondIncidence, huv, source]

@[simp, grind =]
lemma firstIncidence_target : (firstIncidence e u v).target = v := by
  by_cases huv : u = v <;> simp [firstIncidence, huv, target]

@[simp, grind =]
lemma secondIncidence_target : (secondIncidence e u v).target = u := by
  by_cases huv : u = v <;> simp [secondIncidence, huv, target]

@[simp, grind .]
lemma firstIncidence_ne_secondIncidence : firstIncidence e u v ≠ secondIncidence e u v := by
  by_cases huv : u = v <;> simp [firstIncidence, secondIncidence, huv]

omit [DecidableEq V]
lemma isLink_iff_exists_incidenceType : G.IsLink e u v ↔ ∃ i j : Incidence V E, i ≠ j ∧
    G.IsLink i.edge i.source i.target ∧ G.IsLink j.edge j.source j.target ∧
    (G.IsLink i.edge i.source i.target ∧ i.source = u ∧ i.edge = e) ∧
    (G.IsLink j.edge j.source j.target ∧ j.source = v ∧ j.edge = e) := by
    classical
    refine ⟨fun h => ?_, fun ⟨i, j, hij, hi, hj, hi', hj'⟩ => ?_⟩
    · use firstIncidence e u v, secondIncidence e u v, firstIncidence_ne_secondIncidence e u v, ?_,
        ?_, ⟨?_, firstIncidence_source e u v, firstIncidence_edge e u v⟩, ?_,
        secondIncidence_source e u v, secondIncidence_edge e u v <;> simp [h, h.symm]
    obtain ⟨-, rfl, rfl⟩ := hi'
    obtain ⟨-, rfl, he⟩ := hj'
    have := hi.eq_and_eq_or_eq_and_eq (he ▸ hj)
    obtain heq | hne := eq_or_ne i.source i.target
    · grind
    obtain ⟨hs, ht⟩ | ⟨hs, ht⟩ := this.symm
    · grind
    have hjne : j.source ≠ j.target := by grind
    grind [dir_of_ne hne, dir_of_ne hjne]

end firstSecondIncidence

@[simps]
instance : HyperGraphLike V (Incidence V E) E (Graph V E) where
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

attribute [grind =] verts_def edges_def isSource_def isTarget_def isLink_def adj_def

@[simp high, grind .]
lemma mem_edgeFun_firstIncidence_iff [DecidableEq V] :
    f ∈ edgeFun G (firstIncidence e u v) ↔ G.IsLink e u v ∧ e = f := by
  simp [isIncident_def]

@[simp high, grind .]
lemma mem_edgeFun_secondIncidence_iff [DecidableEq V] :
    f ∈ edgeFun G (secondIncidence e u v) ↔ G.IsLink e u v ∧ e = f := by
  simp [isIncident_def, isLink_comm]

lemma edgeFun_preimage_singleton_eq_fwd_bwd_of_isLink_loop (h : G.IsLink e x x) :
    (edgeFun G).preimage {e} = {fwd e x, bwd e x} := by
  ext i
  rcases i with ⟨e₀, u, v, huv⟩ | ⟨e₀, v⟩ | ⟨e₀, v⟩ <;>
  simp [IsIncident] <;>
  grind [IsLink.eq_and_eq_or_eq_and_eq, edge, source,
    target]

lemma edgeFun_preimage_singleton_eq_dir_of_isLink_nonloop (h : G.IsLink e x y) (hxy : x ≠ y) :
    (edgeFun G).preimage {e} = {dir e x y hxy, dir e y x (Ne.symm hxy)} := by
  ext i
  rcases i with ⟨e₀, u, v, huv⟩ | ⟨e₀, v⟩ | ⟨e₀, v⟩ <;>
  simp [IsIncident] <;>
  grind [IsLink.eq_and_eq_or_eq_and_eq, edge, source,
    target, IsLink.symm]

lemma order_eq_two_of_isLink (h : G.IsLink e x y) : order G e = 2 := by
  rw [order]
  obtain rfl | hne := eq_or_ne x y
  · rw [edgeFun_preimage_singleton_eq_fwd_bwd_of_isLink_loop h]
    exact Set.encard_pair (by grind)
  rw [edgeFun_preimage_singleton_eq_dir_of_isLink_nonloop h hne]
  exact Set.encard_pair (by grind)

instance : GraphLike V (Incidence V E) E (Graph V E) where
  order_eq_two G e he := by
    obtain ⟨x, y, h⟩ := exists_isLink_of_mem_edgeSet he
    exact order_eq_two_of_isLink h
  exists_isSource_of_mem_edgeSet G e he := by
    obtain ⟨x, y, h⟩ := exists_isLink_of_mem_edgeSet he
    classical
    exact ⟨firstIncidence e x y, by simpa, by simpa [IsSource]⟩
  exists_isTarget_of_mem_edgeSet G e he := by
    obtain ⟨x, y, h⟩ := exists_isLink_of_mem_edgeSet he
    classical
    exact ⟨secondIncidence e x y, by simpa, by simp [IsTarget, h.symm]⟩

instance : Undirected V (Incidence V E) E (Graph V E) where
  isSource_iff G i := by simp [IsSource, IsTarget]

end Graph
