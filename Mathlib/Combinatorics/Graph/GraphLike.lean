/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon, Laura Monk, Freddie Nash
-/
module

public import Mathlib.Combinatorics.GraphLike.Symm
public import Mathlib.Combinatorics.Graph.Basic

/-!
We define a `Dart` type as a directed edge, and a `GraphLike` instance for `Graph`.
-/

public section

variable {α β γ : Type*} {G : Graph α β}

namespace Graph

/-- `Graph.Dart` is a type for darts or length 1 walks of `Graph`. Every edge of a graph is composed
  of two darts: for loops, there are `fwd` and `bwd` darts, and for non-loops, there are two `dir`
  darts. -/
inductive Dart (α β : Type*) : Type _ where
  | dir : β → ∀ (u v : α), u ≠ v → Dart α β
  | fwd : β → α → Dart α β
  | bwd : β → α → Dart α β

open Dart GraphLike SymmGraphLike

@[simps (attr := grind =) -isSimp]
instance : SymmGraphLike α (Dart α β) β (Graph α β) where
  src d := match d with
    | dir _ u _ _ => u
    | fwd _ u => u
    | bwd _ u => u
  tgt d := match d with
    | dir _ _ v _ => v
    | fwd _ v => v
    | bwd _ v => v
  edge d := match d with
    | dir e _ _ _ => e
    | fwd e _ => e
    | bwd e _ => e
  inv d := match d with
    | dir e u v h => dir e v u h.symm
    | fwd e u => bwd e u
    | bwd e u => fwd e u
  inv_invol := by grind
  inv_src d := by grind
  inv_tgt d := by grind
  verts G := V(G)
  darts G :=
    let s : Dart α β → α := fun d ↦ match d with
      | dir _ u _ _ => u
      | fwd _ u => u
      | bwd _ u => u
    let t : Dart α β → α := fun d ↦ match d with
      | dir _ _ v _ => v
      | fwd _ v => v
      | bwd _ v => v
    let e : Dart α β → β := fun d ↦ match d with
      | dir e _ _ _ => e
      | fwd e _ => e
      | bwd e _ => e
    {d : Dart α β | G.IsLink (e d) (s d) (t d)}
  edges G := E(G)
  src_mem_of_darts _ _ := IsLink.left_mem
  tgt_mem_of_darts _ _ := IsLink.right_mem
  edge_mem_of_darts _ _ := IsLink.edge_mem
  inv_ne G d hd := by grind
  inv_mem_darts_iff G d := by grind [isLink_comm]
  edge_eq_edge_iff G d d' hd hd' := by
    cases d <;> cases d' <;> grind [IsLink.eq_and_eq_or_eq_and_eq]
  Adj G u v := G.Adj u v
  exists_darts_iff_adj G u v := by
    refine ⟨fun ⟨d, hd, hu, hv⟩ ↦ hu ▸ hv ▸ hd.adj, fun ⟨e, he⟩ => ?_⟩
    obtain rfl | hne := eq_or_ne u v
    · exact ⟨Dart.fwd e u, by grind⟩
    exact ⟨Dart.dir e u v hne, by grind⟩

end Graph
