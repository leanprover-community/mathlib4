/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon, Peter Nelson
-/
module

public import Mathlib.Combinatorics.Graph.Subgraph
public import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# Simple graphs

This file defines two type classes for graphs `Graph α β`: `Loopless` and `Simple`.

## Main definitions
- `Loopless`: a graph is loopless if it has no loops
- `Simple`: a graph is simple if it has no multiple edges between the same pair of vertices
- `toSimpleGraph`: a function that constructs a `SimpleGraph V(G)` from a Graph `G`
- `ofSimpleGraph`: a function that constructs a `Graph α (Sym2 α)` from a `SimpleGraph α`

TODO: Show `ofSimpleGraph (toSimpleGraph G)` is isomorphic to `G` when isomorphism on `Graph` is
defined.
-/

public section

variable {α β : Type*} {G H : Graph α β} {u v : α} {e f : β} {X Y : Set α}

open Set SimpleGraph

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

lemma vertexSet_nontrivial_of_edgeSet_nonempty_of_loopless [G.Loopless] (hE : E(G).Nonempty) :
    V(G).Nontrivial := by
  obtain ⟨e, he⟩ := hE
  obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet he
  exact ⟨x, hxy.left_mem, y, hxy.right_mem, hxy.adj.ne⟩

lemma Loopless.anti [hG : G.Loopless] (hle : H ≤ G) : H.Loopless := by
  rw [loopless_iff_forall_ne_of_adj] at hG ⊢
  exact fun x y hxy ↦ hG x y <| hxy.mono hle

@[simp]
lemma Inc.isNonloopAt [G.Loopless] (h : G.Inc e u) : G.IsNonloopAt e u :=
  h.isLoopAt_or_isNonloopAt.resolve_left (Loopless.not_isLoopAt _ _)

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

lemma Simple.anti (hle : H ≤ G) : H.Simple where
  not_isLoopAt e x := by simp [toLoopless.anti hle]
  eq_of_isLink e f x y he hf := (he.mono hle).eq (hf.mono hle)

instance (V : Set α) : (Graph.noEdge V β).Simple where
  not_isLoopAt := by simp [IsLoopAt]
  eq_of_isLink := by simp

instance : (⊥ : Graph α β).Simple := inferInstanceAs (Graph.noEdge _ β).Simple

end Simple

section toSimpleGraph

/-- Construct a simple graph from a graph. -/
@[expose, simps (attr := grind =)]
def toSimpleGraph (G : Graph α β) : SimpleGraph V(G) where
  Adj u v := u ≠ v ∧ G.Adj u v
  symm := ⟨fun u v ↦ by grind [adj_comm]⟩

lemma toSimpleGraph_adj_iff [G.Loopless] (u v : V(G)) : G.toSimpleGraph.Adj u v ↔ G.Adj u v := by
  grind [Adj.ne]

lemma toSimpleGraph_mono (h : G ≤s H) : G.toSimpleGraph ≤ h.vertexSet_eq ▸ H.toSimpleGraph := by
  rintro u v hadj
  match G, H with
  | ⟨GV, GL, GE, _, _, _, _⟩, ⟨HV, HL, HE, _, _, _, _⟩ =>
    obtain ⟨hne, hadj⟩ := toSimpleGraph_adj .. ▸ hadj
    obtain ⟨hle, h⟩ := h
    simp only at h
    subst GV
    simp [toSimpleGraph_adj, hne, hadj.mono hle]

/-- Construct a graph from a simple graph. It has every element of the vertex type as a vertex. -/
@[expose, simps (attr := grind =)]
def ofSimpleGraph (G : SimpleGraph α) : Graph α (Sym2 α) where
  vertexSet := Set.univ
  edgeSet := G.edgeSet
  IsLink e x y := e = s(x, y) ∧ e ∈ G.edgeSet
  isLink_symm e he := ⟨fun u v ↦ by simp [Sym2.eq_swap]⟩
  eq_or_eq_of_isLink_of_isLink e u v x y he hf := by grind
  edge_mem_iff_exists_isLink e := by induction e with | h u v => grind

@[simp]
lemma ofSimpleGraph_adj_iff {G : SimpleGraph α} (u v : α) :
    (ofSimpleGraph G).Adj u v ↔ G.Adj u v := by simp [Adj]

/-- The isomorphism between `toSimpleGraph (ofSimpleGraph G)` and `G`. -/
def toSimpleGraphOfSimpleGraphIso (G : SimpleGraph α) :
    (toSimpleGraph (ofSimpleGraph G)) ≃g G := by
  use Equiv.Set.univ α
  refine ⟨fun h ↦ ⟨fun h' ↦ h.ne (congrArg Subtype.val h'), ?_⟩, fun ⟨_, h⟩ ↦ ?_⟩ <;>
    revert h <;> rw [ofSimpleGraph_adj_iff] <;> exact id

end toSimpleGraph

end Graph
