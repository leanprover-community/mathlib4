/-
Copyright (c) 2026 Snir Broshi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Snir Broshi
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Data.ENat.Lattice

/-!
# Degrees

## Main definitions

* `G.edegree v`: The extended degree of `v` in `G`: the number of vertices adjacent to `v`,
  or `⊤` if there are infinitely many.
-/

public section

namespace SimpleGraph

variable {V W : Type*} (G G' : SimpleGraph V) (H : SimpleGraph W) (u v : V)

/-- `G.edegree v` is the extended degree of `v` in `G`: the number of vertices adjacent to `v`,
or `⊤` if there are infinitely many. -/
noncomputable def edegree : ℕ∞ :=
  G.neighborSet v |>.encard

@[simp]
theorem encard_neighborSet : (G.neighborSet v).encard = G.edegree v := by
  rfl

variable {G v} in
theorem edegree_eq_zero_iff_neighborSet_eq_empty : G.edegree v = 0 ↔ G.neighborSet v = ∅ :=
  Set.encard_eq_zero

variable {G v} in
theorem edegree_ne_zero_iff_nonempty_neighborSet : G.edegree v ≠ 0 ↔ (G.neighborSet v).Nonempty :=
  Set.encard_ne_zero

variable {G v} in
theorem edegree_ne_zero_iff_exists_adj : G.edegree v ≠ 0 ↔ ∃ u, G.Adj v u :=
  edegree_ne_zero_iff_nonempty_neighborSet

variable {G u v} in
theorem Adj.edegree_ne_zero_left (h : G.Adj u v) : G.edegree u ≠ 0 :=
  edegree_ne_zero_iff_nonempty_neighborSet.mpr ⟨_, h⟩

variable {G u v} in
theorem Adj.edegree_ne_zero_right (h : G.Adj u v) : G.edegree v ≠ 0 :=
  h.symm.edegree_ne_zero_left

variable {G v} in
theorem edegree_ne_zero_iff_mem_support : G.edegree v ≠ 0 ↔ v ∈ G.support := by
  rw [edegree_ne_zero_iff_exists_adj, mem_support]

variable {G v} in
theorem edegree_eq_zero_iff_notMem_support : G.edegree v = 0 ↔ v ∉ G.support := by
  rw [← edegree_ne_zero_iff_mem_support, not_ne_iff]

variable {G v} in
theorem nontrivial_of_edegree_ne_zero (h : G.edegree v ≠ 0) : Nontrivial V := by
  have ⟨u, hadj⟩ := edegree_ne_zero_iff_exists_adj.mp h
  exact ⟨_, _, hadj.ne⟩

@[simp]
theorem edegree_eq_zero_of_subsingleton [Subsingleton V] : G.edegree v = 0 := by
  by_contra!
  exact not_nontrivial V <| nontrivial_of_edegree_ne_zero this

variable {G v} in
theorem edegree_eq_one_iff_existsUnique_adj : G.edegree v = 1 ↔ ∃! u, G.Adj v u := by
  simp [← encard_neighborSet, Set.encard_eq_one, Set.singleton_iff_unique_mem]

variable {G v} in
theorem edegree_ne_top_iff_finite_neighborSet : G.edegree v ≠ ⊤ ↔ (G.neighborSet v).Finite :=
  Set.encard_ne_top_iff

theorem edegree_ne_top_of_finite [Finite V] : G.edegree v ≠ ⊤ :=
  edegree_ne_top_iff_finite_neighborSet.mpr <| Set.toFinite _

theorem coe_degree_eq_edegree [Fintype <| G.neighborSet v] : G.degree v = G.edegree v := by
  simp [← encard_neighborSet, ← card_neighborSet_eq_degree]

variable {G v} in
theorem edegree_eq_coe_iff [Fintype <| G.neighborSet v] {n : ℕ} :
    G.edegree v = n ↔ G.degree v = n := by
  simp [← encard_neighborSet, ← Set.coe_fintypeCard]

theorem coe_toNat_edegree_of_finite_neighborSet (h : G.neighborSet v |>.Finite) :
    (G.edegree v).toNat = G.edegree v :=
  h.encard_eq_coe.symm

@[simp]
theorem toNat_edegree [Fintype <| G.neighborSet v] : (G.edegree v).toNat = G.degree v := by
  simp [← encard_neighborSet, ← Set.ncard_def]

theorem edegree_le_card : G.edegree v ≤ ENat.card V := by
  grw [← encard_neighborSet, Set.encard_le_card]

theorem edegree_lt_card_of_ne_top (h : G.edegree v ≠ ⊤) : G.edegree v < ENat.card V :=
  edegree_ne_top_iff_finite_neighborSet.mp h |>.encard_lt_card <| G.neighborSet_ne_univ v

@[simp]
theorem encard_incidenceSet : (G.incidenceSet v).encard = G.edegree v := by
  classical
  simp [Set.encard_congr <| G.incidenceSetEquivNeighborSet v]

theorem edegree_le_encard_edgeSet : G.edegree v ≤ G.edgeSet.encard := by
  grw [← encard_incidenceSet, incidenceSet_subset]

variable {G H} in
theorem Copy.edegree_le (f : Copy G H) (v : V) : G.edegree v ≤ H.edegree (f v) :=
  f.mapNeighborSet v |>.encard_le

variable {G H} in
@[simp]
theorem Iso.edegree_eq (f : G ≃g H) (v : V) : H.edegree (f v) = G.edegree v :=
  (Set.encard_congr <| f.mapNeighborSet v).symm

variable {G G'} in
@[gcongr]
theorem edegree_mono (hle : G ≤ G') (v : V) : G.edegree v ≤ G'.edegree v :=
  Copy.ofLE G G' hle |>.edegree_le v

@[simp]
theorem edegree_top : edegree ⊤ v = ENat.card V - 1 := by
  rw [← encard_neighborSet, neighborSet_top, ← Set.encard_ne_add_one v, ← Set.compl_singleton_eq]
  cases Set.encard {v}ᶜ <;> norm_cast

@[simp]
theorem edegree_bot : edegree ⊥ v = 0 := by
  simp [← encard_neighborSet]

variable {G} in
theorem IsRegularOfDegree.edegree_eq [G.LocallyFinite] {d : ℕ} (h : G.IsRegularOfDegree d) (v : V) :
    G.edegree v = d :=
  edegree_eq_coe_iff.mpr <| h.degree_eq v

end SimpleGraph
