/-
Copyright (c) 2024 Pim Otte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pim Otte
-/
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Represents
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
  simpa [← Set.disjoint_compl_right_iff_subset, Set.compl_eq_univ_diff] using
    Subtype.coe_image_subset _ s

/-- A component of the graph with universal vertices is even if we remove a set of representatives
of odd components and a subset of universal vertices.

This is because the number of vertices in the even components is not affected, and from odd
components exactly one vertex is removed. -/
lemma even_ncard_image_val_supp_sdiff_image_val_rep_union {t : Set V}
    {s : Set G.deleteUniversalVerts.verts} (K : G.deleteUniversalVerts.coe.ConnectedComponent)
    (h : t ⊆ G.universalVerts)
    (hrep : ConnectedComponent.Represents s G.deleteUniversalVerts.coe.oddComponents) :
    Even (Subtype.val '' K.supp \ (Subtype.val '' s ∪ t)).ncard := by
  simp [-deleteUniversalVerts_verts, ← Set.diff_inter_diff, ← Set.image_diff Subtype.val_injective,
    sdiff_eq_left.mpr <| Set.disjoint_of_subset_right h (disjoint_image_val_universalVerts _),
    Set.inter_diff_distrib_right, ← Set.image_inter Subtype.val_injective,
    Set.ncard_image_of_injective _ Subtype.val_injective, K.even_ncard_supp_sdiff_rep hrep]

end SimpleGraph
