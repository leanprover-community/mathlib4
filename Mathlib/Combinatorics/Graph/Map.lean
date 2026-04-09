/-
Copyright (c) 2025 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon, Peter Nelson
-/
module

public import Mathlib.Combinatorics.Graph.Subgraph

/-!
# vertex map on graphs

This file develops the basic theory of vertex maps on graphs `Graph α β`.

## Main definitions
- `map`: the map on graphs induced by a function `f : α → α'`

-/

public section

variable {α α' α'' β : Type*} {G H : Graph α β} {G' H' : Graph α' β} {f g : α → α'}
  {f' g' : α' → α''} {u v w : α} {e : β} {x y : α'} {X Y : Set α}

open Set

namespace Graph

section Map

/-- Map `G : Graph α β` to a `Graph α' β` with the same edge set by applying a function `f : α → α'`
  to each vertex. Edges between identified vertices become loops. -/
@[expose, simps (attr := grind =)]
def map (f : α → α') (G : Graph α β) : Graph α' β where
  vertexSet := f '' V(G)
  edgeSet := E(G)
  IsLink e x' y' := ∃ x y, G.IsLink e x y ∧ x' = f x ∧ y' = f y
  isLink_symm := by
    rintro e he - - ⟨x, y, h, rfl, rfl⟩
    exact ⟨y, x, h.symm, rfl, rfl⟩
  eq_or_eq_of_isLink_of_isLink := by
    rintro e - - - - ⟨x, y, hxy, rfl, rfl⟩ ⟨z, w, hzw, rfl, rfl⟩
    obtain rfl | rfl := hxy.left_eq_or_eq hzw <;> simp
  edge_mem_iff_exists_isLink e := by
    refine ⟨fun h ↦ ?_, ?_⟩
    · obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet h
      exact ⟨_, _, _, _, hxy, rfl, rfl⟩
    rintro ⟨-, -, x, y, h, rfl, rfl⟩
    exact h.edge_mem
  left_mem_of_isLink := by
    rintro e - - ⟨x, y, h, rfl, rfl⟩
    exact Set.mem_image_of_mem _ h.left_mem

@[simp]
lemma map_inc : (G.map f).Inc e x ↔ ∃ v, G.Inc e v ∧ x = f v := by
  simp only [Inc, map_isLink]
  tauto

@[simp]
lemma map_vertexSet_subset (h : X ⊆ V(G)) : f '' X ⊆ V(G.map f) := by
  rw [map_vertexSet]
  gcongr

lemma IsLink.map (h : G.IsLink e u v) (f : α → α') : (G.map f).IsLink e (f u) (f v) :=
  ⟨u, v, h, rfl, rfl⟩

@[simp]
lemma map_isLoopAt : (G.map f).IsLoopAt e x ↔ ∃ u v, G.IsLink e u v ∧ x = f u ∧ x = f v := Iff.rfl

@[gcongr]
lemma map_congr_left_of_eqOn (h : EqOn f g V(G)) : G.map f = G.map g := by
  refine Graph.ext (by grind) fun e x y ↦ ⟨fun ⟨v, w, hvw, _, _⟩ ↦ ?_, fun ⟨v, w, hvw, _, _⟩ ↦ ?_⟩
  <;> subst x y
  · use v, w, hvw, h hvw.left_mem, h hvw.right_mem
  · use v, w, hvw, (h hvw.left_mem).symm, (h hvw.right_mem).symm

@[simp] lemma map_id : (G.map id) = G := by ext a b c <;> simp

@[simp] lemma map_map : (G.map f).map f' = G.map (f' ∘ f) := by ext a b c <;> simp

@[gcongr]
lemma map_mono (h : G ≤ H) : G.map f ≤ H.map f where
  vertexSet_mono v := by
    simp only [map_vertexSet, mem_image, forall_exists_index, and_imp]
    rintro u hu rfl
    use u, h.vertexSet_mono hu
  isLink_mono e x y := by
    simp only [map_isLink, forall_exists_index, and_imp]
    rintro a b hab rfl rfl
    use a, b, h.isLink_mono hab

@[gcongr]
lemma map_isSpanningSubgraph (hsle : G ≤s H) : G.map f ≤s H.map f where
  toIsSubgraph := map_mono hsle.le
  vertexSet_eq := by simp [hsle.vertexSet_eq]

end Map

end Graph
