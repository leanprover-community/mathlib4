/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Mathlib.Combinatorics.GraphLike.Basic
public import Mathlib.Combinatorics.Digraph.Basic

/-!
In this file we make `Digraph` an instance of `GraphLike`. Every adjacent pair is a dart and an
edge.
-/

public section

open GraphLike

namespace Digraph

variable {V : Type*} {G : Digraph V}

instance : GraphLike V (V × V) (V × V) (Digraph V) where
  verts _ := Set.univ
  darts G := { (u, v) | G.Adj u v }
  edges G := { (u, v) | G.Adj u v }
  src_mem_of_darts _ _ _ := Set.mem_univ _
  tgt_mem_of_darts _ _ _ := Set.mem_univ _
  edge_mem_of_darts _ _ := id
  Adj G := G.Adj
  exists_darts_iff_adj := by simp

lemma darts_def (G : Digraph V) : D(G) = { (u, v) | G.Adj u v } := rfl

lemma edges_def (G : Digraph V) : E(G) = { (u, v) | G.Adj u v } := rfl

end Digraph
