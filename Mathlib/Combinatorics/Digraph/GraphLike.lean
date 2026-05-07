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

instance : NoMultiEdgeGraphLike V (V × V) (V × V) (Digraph V) where
  verts _ := Set.univ
  darts G := { (u, v) | G.Adj u v }
  edges G := { (u, v) | G.Adj u v }
  src d := d.fst
  tgt d := d.snd
  edge d := (d.fst, d.snd)
  src_mem_of_darts _ _ _ := Set.mem_univ _
  tgt_mem_of_darts _ _ _ := Set.mem_univ _
  edge_mem_of_darts _ _ := id
  Adj G := G.Adj
  exists_darts_iff_adj := by simp
  src_tgt_inj := Function.injective_id

@[simp, grind =] lemma src_eq (d : V × V) : src (Digraph V) d = d.fst := rfl

@[simp, grind =] lemma tgt_eq (d : V × V) : tgt (Digraph V) d = d.snd := rfl

@[simp]
lemma toProd_eq (d : D(G)) : toProd d = (src (Digraph V) d.val, tgt (Digraph V) d.val) := rfl

@[simp, grind =] lemma edge_eq (d : V × V) : edge (Digraph V) d = d := rfl

@[simp]
lemma val_step_eq {s : step G u v} : s.val = (u, v) := by
  let s' : step G u v := ⟨(u, v), by simp [s.adj], rfl, rfl⟩
  rw [Subsingleton.elim s s']

lemma verts_def (G : Digraph V) : verts G = Set.univ := rfl

lemma darts_def (G : Digraph V) : D(G) = { (u, v) | G.Adj u v } := rfl

lemma edges_def (G : Digraph V) : E(G) = { (u, v) | G.Adj u v } := rfl

end Digraph
