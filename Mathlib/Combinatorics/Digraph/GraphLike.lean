/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Mathlib.Combinatorics.GraphLike.Basic
public import Mathlib.Combinatorics.Digraph.Basic

/-!
In this file we make `Digraph` an instance of `GraphLike`.
-/

@[expose] public section

variable {V : Type*}

namespace Digraph

instance : GraphLike V (V × V) (Digraph V) where
  verts _ := Set.univ
  darts G := { (u, v) | G.Adj u v }
  fst_mem_of_darts _ := Set.mem_univ _
  snd_mem_of_darts _ := Set.mem_univ _
  Adj G := G.Adj
  exists_darts_iff_adj {G : Digraph V} {u v : V} := by simp

lemma darts_def (G : Digraph V) : GraphLike.darts G = { (u, v) | G.Adj u v } := rfl

end Digraph
