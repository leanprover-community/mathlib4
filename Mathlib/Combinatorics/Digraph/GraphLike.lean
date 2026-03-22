/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Mathlib.Combinatorics.GraphLike.Symm
public import Mathlib.Combinatorics.Digraph.Basic

/-!
In this file we make `Digraph` an instance of `GraphLike`.
-/

@[expose] public section

variable {α : Type*}

instance : GraphLike α (α × α) (Digraph α) where
  verts _ := Set.univ
  darts G := { (u, v) | G.Adj u v }
  exists_darts_iff_adj {G : Digraph α} {u v : α} := by simp
  Adj G := G.Adj
  fst_mem_of_darts _ := Set.mem_univ _
  snd_mem_of_darts _ := Set.mem_univ _
