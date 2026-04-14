/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon, Peter Nelson
-/
module

public import Mathlib.Combinatorics.Graph.Subgraph

/-!
# Simple graphs

This file defines two type classes for graphs `Graph α β`: `Loopless` and `Simple`.

## Main definitions
- `Loopless`: a graph is loopless if it has no loops
- `Simple`: a graph is simple if it has no multiple edges between the same pair of vertices

-/

public section

variable {α β : Type*} {G H : Graph α β} {u v : α} {e f : β} {X Y : Set α}

open Set

namespace Graph

section Loopless

/-- A loopless graph is one where the ends of every edge are distinct. -/
@[mk_iff]
protected class Loopless (G : Graph α β) : Prop where
  not_isLoopAt : ∀ e x, ¬ G.IsLoopAt e x

@[simp]
lemma not_isLoopAt (G : Graph α β) [G.Loopless] (e : β) (x : α) : ¬ G.IsLoopAt e x :=
  Loopless.not_isLoopAt e x

lemma not_adj_self (G : Graph α β) [G.Loopless] (x : α) : ¬ G.Adj x x :=
  fun ⟨e, he⟩ ↦ Loopless.not_isLoopAt e x he

lemma Adj.ne [G.Loopless] (hxy : G.Adj u v) : u ≠ v := fun h ↦ G.not_adj_self u <| h ▸ hxy

lemma IsLink.ne [G.Loopless] (he : G.IsLink e u v) : u ≠ v := Adj.ne ⟨e, he⟩

lemma loopless_iff_forall_ne_of_adj : G.Loopless ↔ ∀ u v, G.Adj u v → u ≠ v :=
  ⟨fun _ _ _ h ↦ h.ne, fun h ↦ ⟨fun _ x hex ↦ h x x hex.adj rfl⟩⟩

lemma vertexSet_nontrivial_of_edgeSet_nonempty [G.Loopless] (hE : E(G).Nonempty) :
    V(G).Nontrivial := by
  obtain ⟨e, he⟩ := hE
  obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet he
  exact ⟨x, hxy.left_mem, y, hxy.right_mem, hxy.adj.ne⟩

lemma Loopless.mono (hG : G.Loopless) (hle : H ≤ G) : H.Loopless := by
  rw [loopless_iff_forall_ne_of_adj] at hG ⊢
  exact fun x y hxy ↦ hG x y <| hxy.mono hle

@[simp]
lemma Inc.isNonloopAt [G.Loopless] (h : G.Inc e u) : G.IsNonloopAt e u :=
  h.isLoopAt_or_isNonloopAt.resolve_left (Loopless.not_isLoopAt _ _)

lemma setOf_isLoopAt_eq_empty [G.Loopless] : {e | G.IsLoopAt e u} = ∅ := by ext e; simp

end Loopless

section Simple

/-- A `Simple` graph is a `Loopless` graph where no pair of vertices are the ends of more than one
  edge. -/
@[mk_iff]
class Simple (G : Graph α β) : Prop extends G.Loopless where
  eq_of_isLink : ∀ ⦃e f x y⦄, G.IsLink e x y → G.IsLink f x y → e = f

variable [G.Simple]

lemma IsLink.eq (h : G.IsLink e u v) (h' : G.IsLink f u v) : e = f :=
  Simple.eq_of_isLink h h'

omit [G.Simple] in
lemma Simple.mono (hG : G.Simple) (hle : H ≤ G) : H.Simple where
  not_isLoopAt e x := by simp [hG.toLoopless.mono hle]
  eq_of_isLink e f x y he hf := (he.mono hle).eq (hf.mono hle)

instance (V : Set α) : (Graph.noEdge V β).Simple where
  not_isLoopAt := by simp [IsLoopAt]
  eq_of_isLink := by simp

end Simple

end Graph
