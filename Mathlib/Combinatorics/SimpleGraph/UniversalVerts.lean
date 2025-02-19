/-
Copyright (c) 2024 Pim Otte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pim Otte
-/
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Represents

/-!
# Universal Vertices

This file defines the set of universal vertices: those vertices that are connected
to all others. In addition, it describes results when considering connected components
of the graph where universal vertices are deleted. This particular graph plays a role
in the proof of Tutte's Theorem.

## Main definitions

* `G.universalVerts` is the set of vertices that are connected to all other vertices.
* `G.deleteUniversalVerts` is the subgraph of `G` with the universal vertices removed.
* `G.oddComponents` is the set of connected components of `G` with odd cardinality.
-/

assert_not_exists Field TwoSidedIdeal

namespace SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

/--
The set of vertices that are connected to all other vertices.
-/
def universalVerts (G : SimpleGraph V) : Set V := {v : V | ∀ ⦃w⦄, v ≠ w → G.Adj w v}

lemma isClique_universalVerts (G : SimpleGraph V) : G.IsClique G.universalVerts :=
  fun _ _ _ hy hxy ↦ hy hxy.symm

/--
The subgraph of `G` with the universal vertices removed.
-/
@[simps!]
def deleteUniversalVerts (G : SimpleGraph V) : Subgraph G :=
  (⊤ : Subgraph G).deleteVerts G.universalVerts

lemma Subgraph.IsMatching.exists_of_universalVerts [Finite V] {s : Set V}
    (h : Disjoint G.universalVerts s) (hc : s.ncard ≤ G.universalVerts.ncard) :
    ∃ t ⊆ G.universalVerts, ∃ (M : Subgraph G), M.verts = s ∪ t ∧ M.IsMatching := by
  obtain ⟨t, ht⟩ := Set.exists_subset_card_eq hc
  refine ⟨t, ht.1, ?_⟩
  obtain ⟨f⟩ : Nonempty (s ≃ t) := by
    rw [← Cardinal.eq, ← t.cast_ncard t.toFinite, ← s.cast_ncard s.toFinite, ht.2]
  letI hd := Set.disjoint_of_subset_left ht.1 h
  have hadj (v : s) : G.Adj v (f v) := ht.1 (f v).2 (hd.ne_of_mem (f v).2 v.2)
  exact Subgraph.IsMatching.exists_of_disjoint_sets_of_equiv hd.symm f hadj

lemma disjoint_image_val_universalVerts (s : Set G.deleteUniversalVerts.verts) :
    Disjoint (Subtype.val '' s) G.universalVerts := by
  simpa [deleteUniversalVerts, Subgraph.deleteVerts_verts, ← Set.disjoint_compl_right_iff_subset,
    Set.compl_eq_univ_diff] using Subtype.coe_image_subset _ s

/-- The odd components are the connected components of odd cardinality. This definition excludes
infinite components. -/
def oddComponents : Set G.ConnectedComponent := {c : G.ConnectedComponent | Odd c.supp.ncard}


lemma even_ncard_supp_sdiff_rep [Fintype V] {s : Set V} (K : G.ConnectedComponent)
    (hrep : ConnectedComponent.Represents s G.oddComponents) :
  Even (K.supp \ s).ncard := by
  by_cases h : Even K.supp.ncard
  · simpa [hrep.ncard_sdiff_of_not_mem
      (by simpa [Set.ncard_image_of_injective, ← Nat.not_odd_iff_even] using h)] using h
  · have : K.supp.ncard ≠ 0 := Nat.ne_of_odd_add (Nat.not_even_iff_odd.mp h)
    rw [hrep.ncard_sdiff_of_mem (Nat.not_even_iff_odd.mp h), Nat.even_sub (by omega)]
    simpa [Nat.even_sub]using Nat.not_even_iff_odd.mp h

/-- In this lemma we consider components after deleting universal vertices. If we take
one such component and remove both a set of representatives of odd components and a subset
of -/
lemma even_ncard_supp_sdiff_rep_union [Fintype V] {t : Set V} {s : Set G.deleteUniversalVerts.verts}
    (K : G.deleteUniversalVerts.coe.ConnectedComponent) (h : t ⊆ G.universalVerts)
    (hrep : ConnectedComponent.Represents s G.deleteUniversalVerts.coe.oddComponents) :
  Even ((Subtype.val '' K.supp) \ (Subtype.val '' s ∪ t)).ncard := by
  classical
  simp only [← Set.diff_inter_diff, ← Set.image_diff Subtype.val_injective,
    sdiff_eq_left.mpr <| Set.disjoint_of_subset_right h (disjoint_image_val_universalVerts _),
    Set.inter_diff_distrib_right, Set.inter_self, Set.diff_inter_self_eq_diff,
    ← Set.image_inter Subtype.val_injective, Set.ncard_image_of_injective _ Subtype.val_injective]
  by_cases h : Even K.supp.ncard
  · simpa [hrep.ncard_sdiff_of_not_mem
      (by simpa [Set.ncard_image_of_injective, ← Nat.not_odd_iff_even] using h)] using h
  · have : K.supp.ncard ≠ 0 := Nat.ne_of_odd_add (Nat.not_even_iff_odd.mp h)
    rw [hrep.ncard_sdiff_of_mem (Nat.not_even_iff_odd.mp h), Nat.even_sub (by omega)]
    simpa [Nat.even_sub]using Nat.not_even_iff_odd.mp h



end SimpleGraph
