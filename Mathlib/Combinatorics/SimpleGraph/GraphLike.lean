/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Mathlib.Combinatorics.GraphLike.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
In this file we make `SimpleGraph` an instance of `GraphLike`. Every adjacent pair is a dart and
every adjacent `Sym2 V` is an edge.
-/

public section

variable {V : Type*} {G : SimpleGraph V}

open GraphLike

namespace SimpleGraph

instance : GraphLike V (V × V) (Sym2 V) (SimpleGraph V) where
  verts _ := Set.univ
  darts G := { (u, v) | G.Adj u v }
  edges G := { s | ∃ u v, s = s(u, v) ∧ G.Adj u v }
  src_mem_of_darts _ _ _ := Set.mem_univ _
  tgt_mem_of_darts _ _ _ := Set.mem_univ _
  edge_mem_of_darts G d hd := ⟨d.fst, d.snd, rfl, hd⟩
  Adj G := G.Adj
  exists_darts_iff_adj := by simp

lemma darts_def (G : SimpleGraph V) : D(G) = { (u, v) | G.Adj u v } := rfl

lemma edges_def (G : SimpleGraph V) : E(G) = { s | ∃ u v, s = s(u, v) ∧ G.Adj u v } := rfl

end SimpleGraph
