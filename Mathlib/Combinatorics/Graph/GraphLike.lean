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

open Dart HasSourceTarget HasEdge HasInvol SymmDartLike

instance : SymmDartLike α (Dart α β) where
  src d := match d with
    | dir _ u _ _ => u
    | fwd _ u => u
    | bwd _ u => u
  tgt d := match d with
    | dir _ _ v _ => v
    | fwd _ v => v
    | bwd _ v => v
  symm d := match d with
    | dir e u v h => dir e v u h.symm
    | fwd e u => bwd e u
    | bwd e u => fwd e u
  symm_invol := by grind
  symm_fst := by grind
  symm_snd := by grind

@[grind =]
lemma src_eq (d : Dart α β) : src d = match d with
    | dir _ u _ _ => u
    | fwd _ u => u
    | bwd _ u => u := rfl

@[grind =]
lemma tgt_eq (d : Dart α β) : tgt d = match d with
    | dir _ _ v _ => v
    | fwd _ v => v
    | bwd _ v => v := rfl

@[grind =]
lemma symm_eq (d : Dart α β) : symm d = match d with
    | dir e u v h => dir e v u h.symm
    | fwd e u => bwd e u
    | bwd e u => fwd e u := rfl

instance : HasEdge (Dart α β) β where
  edge d := match d with
    | dir e _ _ _ => e
    | fwd e _ => e
    | bwd e _ => e

@[grind =]
lemma edge_eq (d : Dart α β) : edge d = match d with
    | dir e _ _ _ => e
    | fwd e _ => e
    | bwd e _ => e := rfl

instance : SymmGraphLike α (Dart α β) β (Graph α β) where
  verts G := V(G)
  darts G := {d : Dart α β | G.IsLink (edge d) (src d) (tgt d)}
  edges G := E(G)
  src_mem_of_darts _ _ := IsLink.left_mem
  tgt_mem_of_darts _ _ := IsLink.right_mem
  edge_mem_of_darts _ _ := IsLink.edge_mem
  symm_ne G d hd := by grind
  symm_mem_darts_iff G d := by grind [isLink_comm]
  edge_eq_edge_iff G d d' hd hd' := by
    cases d <;> cases d' <;> grind [IsLink.eq_and_eq_or_eq_and_eq]
  Adj G u v := G.Adj u v
  exists_darts_iff_adj G u v := by
    refine ⟨fun ⟨d, hd, hu, hv⟩ ↦ hu ▸ hv ▸ hd.adj, fun ⟨e, he⟩ => ?_⟩
    obtain rfl | hne := eq_or_ne u v
    · exact ⟨Dart.fwd e u, by grind⟩
    exact ⟨Dart.dir e u v hne, by grind⟩

end Graph
