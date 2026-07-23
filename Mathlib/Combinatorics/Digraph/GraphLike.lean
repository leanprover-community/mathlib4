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

variable {V : Type*} {G : Digraph V} {u v : V}

@[simps (attr := grind =) -isSimp]
instance : NoMultiEdgeGraphLike V (V × V) (V × V) (Digraph V) where
  verts _ := Set.univ
  darts G := { (u, v) | G.Adj u v }
  edges G := { (u, v) | G.Adj u v }
  source G d := d.fst
  target G d := d.snd
  edge G d := (d.fst, d.snd)
  source_mem_of_darts _ _ _ := Set.mem_univ _
  target_mem_of_darts _ _ _ := Set.mem_univ _
  edge_mem_of_darts _ _ := id
  Adj G := G.Adj
  exists_darts_iff_adj := by simp
  src_tgt_inj _ := Function.injective_id

attribute [simp] source_def target_def edge_def

@[simp] lemma toProd_eq (d : D(G)) : toProd d = d.val := rfl

end Digraph
