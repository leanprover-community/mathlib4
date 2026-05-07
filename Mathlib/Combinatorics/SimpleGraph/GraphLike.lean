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
  src := Prod.fst
  tgt := Prod.snd
  edge d := s(d.fst, d.snd)
  inv := Prod.swap
  inv_invol := Prod.swap_swap
  inv_src d := by simp
  inv_tgt d := by simp
  inv_ne G d hd := by grind [hd.ne]
  inv_mem_darts_iff G d := by simp [G.adj_comm]
  src_mem_of_darts _ _ _ := Set.mem_univ _
  tgt_mem_of_darts _ _ _ := Set.mem_univ _
  src_tgt_inj := Function.injective_id
  edge_mem_of_darts G d hd := by simpa using hd
  edge_eq_edge_iff G d d' hd hd' := by grind
  Adj G := G.Adj
  exists_darts_iff_adj := by simp

end SimpleGraph
