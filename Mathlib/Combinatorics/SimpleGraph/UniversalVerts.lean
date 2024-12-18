/-
Copyright (c) 2024 Pim Otte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pim Otte
-/
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Matching

/-!
# Universal Vertices

This file defines the set of universal vertices: those vertices that are connected
to all others. In addition, it describes results when considering connected components
of the graph where universal vertices are deleted. This particular graph plays a role
in the proof of Tutte's Theorem.

## Main definitions

* `G.universalVerts` is the set of vertices that are connected to all other vertices.
* `G.deleteUniversalVerts` is the subgraph of `G` with the universal vertices removed.
-/

namespace SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

/--
  The set of vertices that are connected to all other vertices.
-/
def universalVerts (G : SimpleGraph V) : Set V := {v : V | ∀ w, v ≠ w → G.Adj w v}

lemma isClique_universalVerts (G : SimpleGraph V) : G.IsClique G.universalVerts :=
  fun x _ _ hy hxy ↦ hy x hxy.symm

/--
  The subgraph of `G` with the universal vertices removed.
-/
@[simps!]
def deleteUniversalVerts (G : SimpleGraph V) : Subgraph G :=
  (⊤ : Subgraph G).deleteVerts G.universalVerts

lemma Subgraph.IsMatching.exists_of_universalVerts [Fintype V] {s : Set V}
    (h : Disjoint G.universalVerts s) (hc : s.ncard ≤ G.universalVerts.ncard) :
    ∃ t ⊆ G.universalVerts, ∃ (M : Subgraph G), M.IsMatching ∧ M.verts = s ∪ t := by
  obtain ⟨t, ht⟩ := Set.exists_subset_card_eq hc
  use t
  refine ⟨ht.1, ?_⟩
  have f : s ≃ t := by
    simp only [← Set.Nat.card_coe_set_eq, Nat.card] at ht
    have : Nonempty (s ≃ t) := by
      rw [← Cardinal.eq]
      exact Cardinal.toNat_injOn (Set.mem_Iio.mpr s.toFinite.lt_aleph0)
        (Set.mem_Iio.mpr t.toFinite.lt_aleph0) ht.2.symm
    exact Classical.arbitrary _
  have hd := (Set.disjoint_of_subset_left ht.1 h).symm
  have hadj : ∀ (v : s), G.Adj v (f v) := by
    intro v
    have : ((f v) : V) ∈ G.universalVerts := ht.1 (f v).coe_prop
    simp only [universalVerts, Set.mem_setOf_eq] at this
    apply this
    exact (Disjoint.ne_of_mem hd v.coe_prop (f v).coe_prop).symm
  obtain ⟨M1, hM1⟩ := Subgraph.IsMatching.exists_of_disjoint_sets_of_equiv hd f hadj
  aesop

end SimpleGraph
