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

public section

open GraphLike

namespace Digraph

variable {V : Type*} {G : Digraph V}

instance : SimpleGraphLike G where
  verts := Set.univ
  darts := { (u, v) | G.Adj u v }
  fst_mem_of_darts _ _ := Set.mem_univ _
  snd_mem_of_darts _ _ := Set.mem_univ _
  Adj := G.Adj
  exists_darts_iff_adj {u v : V} := by simp

lemma darts_def (G : Digraph V) : D(G) = { (u, v) | G.Adj u v } := rfl

end Digraph
