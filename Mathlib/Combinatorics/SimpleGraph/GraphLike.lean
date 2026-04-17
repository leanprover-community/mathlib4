/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Mathlib.Combinatorics.GraphLike.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
In this file we make `SimpleGraph` an instance of `GraphLike`.
-/

public section

variable {V : Type*} {G : SimpleGraph V}

open GraphLike

namespace SimpleGraph

instance : SimpleGraphLike G where
  verts := Set.univ
  darts := { (u, v) | G.Adj u v }
  fst_mem_of_darts _ := Set.mem_univ _
  snd_mem_of_darts _ := Set.mem_univ _
  Adj := G.Adj
  exists_darts_iff_adj {u v : V} := by simp

lemma darts_def (G : SimpleGraph V) : D(G) = { (u, v) | G.Adj u v } := rfl

end SimpleGraph
