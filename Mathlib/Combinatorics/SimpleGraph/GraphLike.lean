/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Mathlib.Combinatorics.GraphLike.Symm
public import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
In this file we make `SimpleGraph` an instance of `GraphLike`. Every adjacent pair is a dart and
every adjacent `Sym2 V` is an edge.
-/

public section

variable {V : Type*} {G : SimpleGraph V}

open GraphLike

namespace SimpleGraph

@[simps (attr := grind =) -isSimp]
instance : noMultiEdgeSymmGraphLike V (V × V) (Sym2 V) (SimpleGraph V) where
  verts _ := Set.univ
  darts G := { (u, v) | G.Adj u v }
  edges G := G.edgeSet
  src G s := s.fst
  tgt G s := s.snd
  edge G s := s(s.fst, s.snd)
  inv s := Prod.swap s
  inv_invol _ := rfl
  inv_src G _ := rfl
  inv_tgt G _ := rfl
  src_mem_of_darts _ _ _ := Set.mem_univ _
  tgt_mem_of_darts _ _ _ := Set.mem_univ _
  edge_mem_of_darts G d hd := by simpa using hd
  src_tgt_inj G := Function.injective_id
  inv_ne G d hd := by grind [hd.ne]
  inv_mem_darts_iff G d := by simp [G.adj_comm]
  edge_eq_edge_iff G d d' hd hd' := by grind
  Adj G := G.Adj
  exists_darts_iff_adj := by simp

attribute [simp] src_def tgt_def edge_def inv_def

@[simp]
lemma val_step_eq {u v : V} (s : Step G u v) : s.val = (u, v) := by
  obtain ⟨d, hd, rfl, rfl⟩ := s
  rfl

@[expose] def Adj.toStep {u v : V} (h : Adj G u v) : Step G u v := ⟨(u, v), by simpa⟩

@[simp]
lemma Adj.toStep_eq {u v : V} (h : Adj G u v) : GraphLike.Adj.toStep h = h.toStep := by
  simp [toStep]

@[simp] lemma toProd_eq (d : D(G)) : toProd d = d.val := rfl

end SimpleGraph
