/-
Copyright (c) 2026 Iván Renison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iván Renison
-/
module

public import Mathlib.Combinatorics.HasAdj.Basic
public import Mathlib.Combinatorics.Digraph.Basic

/-!
In this file we make `Digraph` an instance of `HasAdj`.
-/

@[expose] public section

variable {α : Type*}

instance : HasAdj α (Digraph α) where
  vertexSet _ := Set.univ
  Adj G := G.Adj
  left_mem_vertexSet_of_adj _ := Set.mem_univ _
  right_mem_vertexSet_of_adj _ := Set.mem_univ _
