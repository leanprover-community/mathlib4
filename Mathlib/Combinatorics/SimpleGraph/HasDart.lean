/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Mathlib.Combinatorics.HasDart.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
In this file we make `SimpleGraph` an instance of `HasDart`.
-/

@[expose] public section

variable {α : Type*}

instance : HasDart α (SimpleGraph α) where
  verts _ := Set.univ
  Adj G := G.Adj
  dart G u v := G.Adj u v
  nonempty_dart_iff_adj := nonempty_prop
  left_mem_verts_of_adj _ {u _ : α} _ := Set.mem_univ u
  right_mem_verts_of_adj _ {_ v : α} _ := Set.mem_univ v
