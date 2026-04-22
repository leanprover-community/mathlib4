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
* `G.maxEDegree`: The maximum extended degree of all vertices, or `0` if there are no vertices.
* `G.minEDegree`: The minimum extended degree of all vertices, or `⊤` if there are no vertices.
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
@[simp]
theorem edegree_eq_zero_iff_isIsolated : G.edegree v = 0 ↔ G.IsIsolated v := by
  simp [← encard_neighborSet]

alias ⟨_, IsIsolated.edegree_eq⟩ := edegree_eq_zero_iff_isIsolated

variable {G u v} in
theorem Adj.edegree_ne_zero_left (h : G.Adj u v) : G.edegree u ≠ 0 :=
  edegree_eq_zero_iff_isIsolated.not.mpr h.not_isIsolated_left

variable {G u v} in
theorem Adj.edegree_ne_zero_right (h : G.Adj u v) : G.edegree v ≠ 0 :=
  h.symm.edegree_ne_zero_left

variable {G v} in
theorem nontrivial_of_edegree_ne_zero (h : G.edegree v ≠ 0) : Nontrivial V :=
  nontrivial_of_not_isIsolated <| edegree_eq_zero_iff_isIsolated.not.mp h

@[simp]
theorem edegree_eq_zero_of_subsingleton [Subsingleton V] (G : SimpleGraph V) (v : V) :
    G.edegree v = 0 :=
  edegree_eq_zero_iff_isIsolated.mpr <| .of_subsingleton G v

variable {G v} in
theorem edegree_eq_one_iff_existsUnique_adj : G.edegree v = 1 ↔ ∃! u, G.Adj v u := by
  simp [← encard_neighborSet, Set.encard_eq_one, Set.singleton_iff_unique_mem]

variable {G v} in
theorem edegree_ne_top_iff_finite_neighborSet : G.edegree v ≠ ⊤ ↔ (G.neighborSet v).Finite :=
  Set.encard_ne_top_iff

theorem edegree_ne_top_of_finite [Finite V] (G : SimpleGraph V) (v : V) : G.edegree v ≠ ⊤ :=
  edegree_ne_top_iff_finite_neighborSet.mpr <| Set.toFinite _

theorem coe_degree_eq_edegree [Fintype <| G.neighborSet v] : G.degree v = G.edegree v := by
  simp [← encard_neighborSet, ← card_neighborSet_eq_degree]

variable {G v} in
theorem edegree_eq_coe_iff [Fintype <| G.neighborSet v] {n : ℕ} :
    G.edegree v = n ↔ G.degree v = n := by
  simp [← coe_degree_eq_edegree]

@[simp]
theorem toNat_edegree [Fintype <| G.neighborSet v] : (G.edegree v).toNat = G.degree v := by
  simp [← coe_degree_eq_edegree]

theorem coe_toNat_edegree_eq_self :
    (G.edegree v).toNat = G.edegree v ↔ (G.neighborSet v).Finite := by
  simp [edegree_ne_top_iff_finite_neighborSet]

theorem edegree_le_card : G.edegree v ≤ ENat.card V := by
  grw [← encard_neighborSet, Set.encard_le_card]

variable {v} in
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

theorem eq_bot_iff_edegree : G = ⊥ ↔ ∀ v, G.edegree v = 0 := by
  simp [eq_bot_iff_neighborSet, edegree_eq_zero_iff_isIsolated]

variable {G} in
theorem IsRegularOfDegree.edegree_eq [G.LocallyFinite] {d : ℕ} (h : G.IsRegularOfDegree d) (v : V) :
    G.edegree v = d :=
  edegree_eq_coe_iff.mpr <| h.degree_eq v

/-- The maximum extended degree of all vertices, or `0` if there are no vertices -/
noncomputable def maxEDegree : ℕ∞ :=
  ⨆ v, G.edegree v

/-- The minimum extended degree of all vertices, or `⊤` if there are no vertices -/
noncomputable def minEDegree : ℕ∞ :=
  ⨅ v, G.edegree v

theorem maxEDegree_eq_iSup : G.maxEDegree = ⨆ v, G.edegree v := by
  rfl

theorem minEDegree_eq_iInf : G.minEDegree = ⨅ v, G.edegree v := by
  rfl

variable {G} in
@[simp]
theorem maxEDegree_eq_zero_iff_eq_bot : G.maxEDegree = 0 ↔ G = ⊥ := by
  simp [maxEDegree_eq_iSup, eq_bot_iff_edegree]

variable {G} in
theorem minEDegree_eq_zero_iff_support_ne : G.minEDegree = 0 ↔ G.support ≠ .univ := by
  simp [minEDegree_eq_iInf, Set.ne_univ_iff_exists_notMem, notMem_support_iff_isIsolated]

variable {G} in
theorem maxEDegree_eq_top_iff_lt : G.maxEDegree = ⊤ ↔ ∀ n : ℕ, ∃ v, n < G.edegree v :=
  WithTop.iSup_eq_top_iff_lt

variable {G} in
theorem maxEDegree_eq_top_iff_le : G.maxEDegree = ⊤ ↔ ∀ n : ℕ, ∃ v, n ≤ G.edegree v :=
  WithTop.iSup_eq_top_iff_le

variable {G} in
theorem minEDegree_eq_top_iff : G.minEDegree = ⊤ ↔ ∀ v, G.edegree v = ⊤ :=
  iInf_eq_top

theorem exists_edegree_eq_maxEDegree [Nonempty V] (G : SimpleGraph V) (h : G.maxEDegree ≠ ⊤) :
    ∃ v, G.edegree v = G.maxEDegree :=
  Set.range_nonempty G.edegree |>.csSup_mem <| ENat.finite_of_sSup_lt_top h.lt_top

theorem exists_edegree_eq_minEDegree [Nonempty V] (G : SimpleGraph V) :
    ∃ v, G.edegree v = G.minEDegree :=
  ciInf_mem G.edegree

theorem edegree_le_maxEDegree : G.edegree v ≤ G.maxEDegree :=
  le_iSup G.edegree v

theorem minEDegree_le_edegree : G.minEDegree ≤ G.edegree v :=
  iInf_le G.edegree v

variable {v} in
theorem maxEDegree_eq_top_of_edegree_eq_top (h : G.edegree v = ⊤) : G.maxEDegree = ⊤ :=
  eq_top_iff.mpr <| G.edegree_le_maxEDegree v |>.trans_eq' h

variable {v} in
theorem minEDegree_eq_zero_of_edegree_eq_zero (h : G.edegree v = 0) : G.minEDegree = 0 :=
  nonpos_iff_eq_zero.mp <| G.minEDegree_le_edegree v |>.trans_eq h

theorem maxEDegree_le_of_forall_edegree_le {n : ℕ∞} (h : ∀ v, G.edegree v ≤ n) : G.maxEDegree ≤ n :=
  iSup_le h

theorem le_minEDegree_of_forall_le_edegree {n : ℕ∞} (h : ∀ v, n ≤ G.edegree v) : n ≤ G.minEDegree :=
  le_iInf h

@[simp]
theorem maxEDegree_of_subsingleton [Subsingleton V] (G : SimpleGraph V) : G.maxEDegree = 0 := by
  simp [maxEDegree_eq_iSup]

@[simp]
theorem minEDegree_of_isEmpty [IsEmpty V] (G : SimpleGraph V) : G.minEDegree = ⊤ :=
  iInf_of_empty G.edegree

@[simp]
theorem minEDegree_of_subsingleton_of_nonempty [Subsingleton V] [Nonempty V] (G : SimpleGraph V) :
    G.minEDegree = 0 := by
  simp [minEDegree_eq_iInf]

theorem maxEDegree_ne_top_of_finite [Finite V] (G : SimpleGraph V) : G.maxEDegree ≠ ⊤ :=
  iSup_ne_top G.edegree_ne_top_of_finite

theorem minEDegree_ne_top_of_finite [Nonempty V] [Finite V] (G : SimpleGraph V) :
    G.minEDegree ≠ ⊤ := by
  rw [minEDegree_eq_iInf, ne_eq, iInf_eq_top, not_forall]
  have ⟨v⟩ := ‹Nonempty V›
  exact ⟨v, G.edegree_ne_top_of_finite v⟩

theorem coe_maxDegree_eq_maxEDegree [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.maxDegree = G.maxEDegree := by
  cases isEmpty_or_nonempty V
  · simp
  rw [maxEDegree_eq_iSup, maxDegree, ← Finset.coe_max' <| by simp, Finset.max'_eq_sup',
    Finset.sup'_image, Finset.sup'_univ_eq_ciSup]
  simpa [← coe_degree_eq_edegree] using ENat.coe_iSup <| Set.finite_range _ |>.bddAbove

theorem coe_minDegree_eq_minEDegree [Nonempty V] [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : G.minDegree = G.minEDegree := by
  rw [minEDegree_eq_iInf, minDegree, ← Finset.coe_min' <| by simp, Finset.min'_eq_inf',
    Finset.inf'_image, Finset.inf'_univ_eq_ciInf]
  simpa [← coe_degree_eq_edegree] using ENat.coe_iInf

variable {G} in
theorem maxEDegree_eq_coe_iff [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] {n : ℕ} :
    G.maxEDegree = n ↔ G.maxDegree = n := by
  simp [← coe_maxDegree_eq_maxEDegree]

variable {G} in
theorem minEDegree_eq_coe_iff [Nonempty V] [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {n : ℕ} : G.minEDegree = n ↔ G.minDegree = n := by
  simp [← coe_minDegree_eq_minEDegree]

variable {G} in
theorem minEDegree_eq_coe_iff_of_neZero [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] {n : ℕ}
    [NeZero n] : G.minEDegree = n ↔ G.minDegree = n := by
  cases isEmpty_or_nonempty V
  · simpa using NeZero.ne' n
  simp [← coe_minDegree_eq_minEDegree]

@[simp]
theorem toNat_maxEDegree [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.maxEDegree.toNat = G.maxDegree := by
  simp [← coe_maxDegree_eq_maxEDegree]

@[simp]
theorem toNat_minEDegree [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.minEDegree.toNat = G.minDegree := by
  cases isEmpty_or_nonempty V
  · simp
  simp [← coe_minDegree_eq_minEDegree]

variable {G H} in
theorem IsContained.maxEDegree_le (h : G ⊑ H) : G.maxEDegree ≤ H.maxEDegree := by
  refine G.maxEDegree_le_of_forall_edegree_le fun v ↦ ?_
  grw [h.some.edegree_le, edegree_le_maxEDegree]

variable {G H} in
theorem Copy.minEDegree_le {f : Copy G H} (hf : Function.Surjective f) :
    G.minEDegree ≤ H.minEDegree := by
  refine H.le_minEDegree_of_forall_le_edegree fun w ↦ ?_
  obtain ⟨v, rfl⟩ := hf w
  grw [← f.edegree_le, ← minEDegree_le_edegree]

variable {G H} in
theorem Hom.minEDegree_le {f : G →g H} (hf : Function.Bijective f) : G.minEDegree ≤ H.minEDegree :=
  Copy.minEDegree_le (f := ⟨f, hf.injective⟩) hf.surjective

variable {G H} in
@[gcongr]
theorem Iso.maxEDegree_eq (f : G ≃g H) : G.maxEDegree = H.maxEDegree :=
  f.toEquiv.iSup_congr f.edegree_eq

variable {G H} in
@[gcongr]
theorem Iso.minEDegree_eq (f : G ≃g H) : G.minEDegree = H.minEDegree :=
  f.toEquiv.iInf_congr f.edegree_eq

variable {G G'} in
@[gcongr]
theorem maxEDegree_mono (hle : G ≤ G') : G.maxEDegree ≤ G'.maxEDegree :=
  IsContained.of_le hle |>.maxEDegree_le

variable {G G'} in
@[gcongr]
theorem minEDegree_mono (hle : G ≤ G') : G.minEDegree ≤ G'.minEDegree :=
  Hom.ofLE hle |>.minEDegree_le Function.bijective_id

theorem maxEDegree_le_card : G.maxEDegree ≤ ENat.card V :=
  G.maxEDegree_le_of_forall_edegree_le G.edegree_le_card

theorem minEDegree_le_card [Nonempty V] (G : SimpleGraph V) : G.minEDegree ≤ ENat.card V := by
  have ⟨v⟩ := ‹Nonempty V›
  grw [G.minEDegree_le_edegree v, edegree_le_card]

variable {G} in
theorem maxEDegree_lt_card_of_ne_top [Nonempty V] (G : SimpleGraph V) (h : G.maxEDegree ≠ ⊤) :
    G.maxEDegree < ENat.card V := by
  have ⟨v, hv⟩ := G.exists_edegree_eq_maxEDegree h
  rw [← hv] at h ⊢
  exact G.edegree_lt_card_of_ne_top h

variable {G} in
theorem minEDegree_lt_card_of_ne_top (h : G.minEDegree ≠ ⊤) : G.minEDegree < ENat.card V := by
  cases isEmpty_or_nonempty V
  · simp at h
  have ⟨v, hv⟩ := G.exists_edegree_eq_minEDegree
  rw [← hv] at h ⊢
  exact G.edegree_lt_card_of_ne_top h

theorem minEDegree_le_encard_edgeSet [Nonempty V] (G : SimpleGraph V) :
    G.minEDegree ≤ G.edgeSet.encard := by
  have ⟨v, hv⟩ := G.exists_edegree_eq_minEDegree
  exact hv ▸ G.edegree_le_encard_edgeSet v

theorem maxEDegree_le_encard_edgeSet : G.maxEDegree ≤ G.edgeSet.encard :=
  maxEDegree_le_of_forall_edegree_le _ G.edegree_le_encard_edgeSet

theorem minEDegree_le_maxEDegree [Nonempty V] (G : SimpleGraph V) :
    G.minEDegree ≤ G.maxEDegree := by
  have ⟨v⟩ := ‹Nonempty V›
  grw [G.minEDegree_le_edegree v, edegree_le_maxEDegree]

@[simp]
theorem maxEDegree_top : (completeGraph V).maxEDegree = ENat.card V - 1 := by
  cases isEmpty_or_nonempty V
  · simp [ENat.card_eq_zero_iff_empty V |>.mpr ‹_›]
  simp [maxEDegree_eq_iSup]

@[simp]
theorem minEDegree_top [Nonempty V] : (completeGraph V).minEDegree = ENat.card V - 1 := by
  simp [minEDegree_eq_iInf]

@[simp]
theorem maxEDegree_bot : (emptyGraph V).maxEDegree = 0 := by
  simp [maxEDegree_eq_iSup]

@[simp]
theorem minEDegree_bot [Nonempty V] : (emptyGraph V).minEDegree = 0 := by
  simp [minEDegree_eq_iInf]

variable {G} in
theorem IsRegularOfDegree.maxEDegree_eq [Nonempty V] [G.LocallyFinite] {d : ℕ}
    (h : G.IsRegularOfDegree d) : G.maxEDegree = d := by
  simp [maxEDegree_eq_iSup, h.edegree_eq]

variable {G} in
theorem IsRegularOfDegree.minEDegree_eq [Nonempty V] [G.LocallyFinite] {d : ℕ}
    (h : G.IsRegularOfDegree d) : G.minEDegree = d := by
  simp [minEDegree_eq_iInf, h.edegree_eq]

end SimpleGraph
