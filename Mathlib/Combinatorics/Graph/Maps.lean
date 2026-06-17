/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon, Peter Nelson
-/
module

public import Mathlib.Combinatorics.Graph.Subgraph

/-!
# Maps between graphs

This file defines vertex map between graphs `Graph α β`. Morphisms between graphs will also be
defined in this file in the future.

## Main definitions

* `map`: the map on graphs induced by a function on vertices `f : α → α'`

## TODO

* Morphisms between graphs

-/

public section

variable {α α' α'' β : Type*} {G H : Graph α β} {f g : α → α'} {u v : α} {e : β} {x y : α'}

open Set Relation

namespace Graph

section Map

/-- Map `G : Graph α β` to a `Graph α' β` with the same edge set by applying a function `f : α → α'`
  to each vertex. Edges between identified vertices become loops. -/
@[expose, simps! (attr := grind =)]
def map (f : α → α') (G : Graph α β) : Graph α' β where
  vertexSet := f '' V(G)
  edgeSet := E(G)
  IsLink e := Relation.Map (G.IsLink e) f f
  isLink_symm _ he := map_symmetric (G.isLink_symm he) f
  eq_or_eq_of_isLink_of_isLink := by
    rintro e - - - - ⟨x, y, hxy, rfl, rfl⟩ ⟨z, w, hzw, rfl, rfl⟩
    obtain rfl | rfl := hxy.left_eq_or_eq hzw <;> simp
  edge_mem_iff_exists_isLink e := by
    refine ⟨fun h ↦ ?_, fun ⟨_, _, _, _, h, _, _⟩ ↦ h.edge_mem⟩
    obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet h
    exact ⟨_, _, _, _, hxy, rfl, rfl⟩
  left_mem_of_isLink := by
    rintro e - - ⟨x, y, h, rfl, rfl⟩
    exact Set.mem_image_of_mem _ h.left_mem

protected lemma IsLink.map (f : α → α') (h : G.IsLink e u v) : (G.map f).IsLink e (f u) (f v) :=
  ⟨u, v, h, rfl, rfl⟩

@[simp]
lemma map_inc (f : α → α') : (G.map f).Inc e x ↔ ∃ v, G.Inc e v ∧ x = f v := by
  simp only [Inc, map_isLink, map_apply]
  tauto

protected lemma Inc.map (f : α → α') (h : G.Inc e v) : (G.map f).Inc e (f v) := by
  obtain ⟨w, hw⟩ := h
  exact ⟨f w, hw.map f⟩

@[simp]
lemma map_isLoopAt (f : α → α') :
    (G.map f).IsLoopAt e x ↔ ∃ u v, G.IsLink e u v ∧ f u = x ∧ f v = x := Iff.rfl

protected lemma IsLoopAt.map (f : α → α') (h : G.IsLoopAt e v) : (G.map f).IsLoopAt e (f v) :=
  IsLink.map f h

@[simp]
lemma map_adj (f : α → α') : (G.map f).Adj x y ↔ Relation.Map G.Adj f f x y := by
  simp only [Adj, map_isLink, map_apply]
  tauto

protected lemma Adj.map (f : α → α') (h : G.Adj u v) : (G.map f).Adj (f u) (f v) := by
  obtain ⟨e, h⟩ := h
  exact ⟨e, h.map f⟩

@[simp] lemma map_id : G.map id = G := by ext a b c <;> simp

@[simp]
lemma map_map (f : α → α') (f' : α' → α'') : (G.map f).map f' = G.map (f' ∘ f) := by
  ext a b c <;> simp [map_apply]

@[gcongr]
protected lemma IsSubgraph.map (f : α → α') (h : G ≤ H) : G.map f ≤ H.map f where
  vertexSet_mono v := by grind [h.vertexSet_mono]
  isLink_mono e := map_mono <| h.isLink_mono (e := e)
alias map_mono := IsSubgraph.map

@[gcongr]
protected lemma IsSpanningSubgraph.map (f : α → α') (hsle : G ≤s H) : G.map f ≤s H.map f where
  le := hsle.le.map f
  vertexSet_eq := by simp [hsle.vertexSet_eq]

@[gcongr]
lemma map_eq_of_eqOn (h : EqOn f g V(G)) : G.map f = G.map g := by
  refine Graph.ext (by grind) fun _ _ _ ↦ ⟨fun ⟨_, _, hvw, _, _⟩ ↦ ?_, fun ⟨_, _, hvw, _, _⟩ ↦ ?_⟩
  <;> grind [h hvw.left_mem, h hvw.right_mem, hvw.map]

end Map

end Graph
