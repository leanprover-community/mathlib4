/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Order.Interval.Set.OrdConnectedComponent
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Separation.Regular

/-!
# Linear order is a completely normal Hausdorff topological space

In this file we prove that a linear order with order topology is a completely normal Hausdorff
topological space.
-/


open Filter Set Function OrderDual Topology Interval

variable {X : Type*} [LinearOrder X] [TopologicalSpace X] [OrderTopology X] {a : X} {s t : Set X}

namespace Set

@[simp]
theorem ordConnectedComponent_mem_nhds : ordConnectedComponent s a ∈ 𝓝 a ↔ s ∈ 𝓝 a := by
  refine ⟨fun h ↦ mem_of_superset h ordConnectedComponent_subset, fun h ↦ ?_⟩
  rcases exists_Icc_mem_subset_of_mem_nhds h with ⟨b, c, ha, ha', hs⟩
  exact mem_of_superset ha' (subset_ordConnectedComponent ha hs)

theorem compl_ordConnectedSection_ordSeparatingSet_mem_nhdsGE (hd : Disjoint s (closure t))
    (ha : a ∈ s) : (ordConnectedSection (ordSeparatingSet s t))ᶜ ∈ 𝓝[≥] a := by
  have hmem : tᶜ ∈ 𝓝[≥] a := by
    refine mem_nhdsWithin_of_mem_nhds ?_
    rw [← mem_interior_iff_mem_nhds, interior_compl]
    exact disjoint_left.1 hd ha
  rcases exists_Icc_mem_subset_of_mem_nhdsGE hmem with ⟨b, hab, hmem', hsub⟩
  by_cases H : Disjoint (Icc a b) (ordConnectedSection <| ordSeparatingSet s t)
  · exact mem_of_superset hmem' (disjoint_left.1 H)
  · simp only [Set.disjoint_left, not_forall, Classical.not_not] at H
    rcases H with ⟨c, ⟨hac, hcb⟩, hc⟩
    have hsub' : Icc a b ⊆ ordConnectedComponent tᶜ a :=
      subset_ordConnectedComponent (left_mem_Icc.2 hab) hsub
    have hd : Disjoint s (ordConnectedSection (ordSeparatingSet s t)) :=
      disjoint_left_ordSeparatingSet.mono_right ordConnectedSection_subset
    replace hac : a < c := hac.lt_of_ne <| Ne.symm <| ne_of_mem_of_not_mem hc <|
      disjoint_left.1 hd ha
    filter_upwards [Ico_mem_nhdsGE hac] with x hx hx'
    refine hx.2.ne (eq_of_mem_ordConnectedSection_of_uIcc_subset hx' hc ?_)
    refine subset_inter (subset_iUnion₂_of_subset a ha ?_) ?_
    · exact OrdConnected.uIcc_subset inferInstance (hsub' ⟨hx.1, hx.2.le.trans hcb⟩)
        (hsub' ⟨hac.le, hcb⟩)
    · rcases mem_iUnion₂.1 (ordConnectedSection_subset hx').2 with ⟨y, hyt, hxy⟩
      refine subset_iUnion₂_of_subset y hyt (OrdConnected.uIcc_subset inferInstance hxy ?_)
      refine subset_ordConnectedComponent left_mem_uIcc hxy ?_
      suffices c < y by
        rw [uIcc_of_ge (hx.2.trans this).le]
        exact ⟨hx.2.le, this.le⟩
      refine lt_of_not_ge fun hyc ↦ ?_
      have hya : y < a := not_le.1 fun hay ↦ hsub ⟨hay, hyc.trans hcb⟩ hyt
      exact hxy (Icc_subset_uIcc ⟨hya.le, hx.1⟩) ha

theorem compl_ordConnectedSection_ordSeparatingSet_mem_nhdsLE (hd : Disjoint s (closure t))
    (ha : a ∈ s) : (ordConnectedSection <| ordSeparatingSet s t)ᶜ ∈ 𝓝[≤] a := by
  have hd' : Disjoint (ofDual ⁻¹' s) (closure <| ofDual ⁻¹' t) := hd
  have ha' : toDual a ∈ ofDual ⁻¹' s := ha
  simpa only [dual_ordSeparatingSet, dual_ordConnectedSection] using
    compl_ordConnectedSection_ordSeparatingSet_mem_nhdsGE hd' ha'

theorem compl_ordConnectedSection_ordSeparatingSet_mem_nhds (hd : Disjoint s (closure t))
    (ha : a ∈ s) : (ordConnectedSection <| ordSeparatingSet s t)ᶜ ∈ 𝓝 a := by
  rw [← nhdsLE_sup_nhdsGE, mem_sup]
  exact ⟨compl_ordConnectedSection_ordSeparatingSet_mem_nhdsLE hd ha,
    compl_ordConnectedSection_ordSeparatingSet_mem_nhdsGE hd ha⟩

theorem ordT5Nhd_mem_nhdsSet (hd : Disjoint s (closure t)) : ordT5Nhd s t ∈ 𝓝ˢ s :=
  bUnion_mem_nhdsSet fun x hx ↦ ordConnectedComponent_mem_nhds.2 <| inter_mem
    (by
      rw [← mem_interior_iff_mem_nhds, interior_compl]
      exact disjoint_left.1 hd hx)
    (compl_ordConnectedSection_ordSeparatingSet_mem_nhds hd hx)

end Set

open Set

/-- A linear order with order topology is a completely normal Hausdorff topological space. -/
instance (priority := 100) OrderTopology.completelyNormalSpace : CompletelyNormalSpace X :=
  ⟨fun s t h₁ h₂ ↦ Filter.disjoint_iff.2
    ⟨ordT5Nhd s t, ordT5Nhd_mem_nhdsSet h₂, ordT5Nhd t s, ordT5Nhd_mem_nhdsSet h₁.symm,
      disjoint_ordT5Nhd⟩⟩

instance (priority := 100) OrderTopology.t5Space : T5Space X := T5Space.mk
