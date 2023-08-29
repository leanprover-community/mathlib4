/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Topology.Order.Basic
import Mathlib.Data.Set.Intervals.OrdConnectedComponent

#align_import topology.algebra.order.t5 from "leanprover-community/mathlib"@"4c19a16e4b705bf135cf9a80ac18fcc99c438514"

/-!
# Linear order is a completely normal Hausdorff topological space

In this file we prove that a linear order with order topology is a completely normal Hausdorff
topological space.
-/


open Filter Set Function OrderDual Topology Interval

variable {X : Type*} [LinearOrder X] [TopologicalSpace X] [OrderTopology X] {a b c : X}
  {s t : Set X}

namespace Set

@[simp]
theorem ordConnectedComponent_mem_nhds : ordConnectedComponent s a ∈ 𝓝 a ↔ s ∈ 𝓝 a := by
  refine' ⟨fun h => mem_of_superset h ordConnectedComponent_subset, fun h => _⟩
  -- ⊢ ordConnectedComponent s a ∈ 𝓝 a
  rcases exists_Icc_mem_subset_of_mem_nhds h with ⟨b, c, ha, ha', hs⟩
  -- ⊢ ordConnectedComponent s a ∈ 𝓝 a
  exact mem_of_superset ha' (subset_ordConnectedComponent ha hs)
  -- 🎉 no goals
#align set.ord_connected_component_mem_nhds Set.ordConnectedComponent_mem_nhds

theorem compl_section_ordSeparatingSet_mem_nhdsWithin_Ici (hd : Disjoint s (closure t))
    (ha : a ∈ s) : (ordConnectedSection (ordSeparatingSet s t))ᶜ ∈ 𝓝[≥] a := by
  have hmem : tᶜ ∈ 𝓝[≥] a := by
    refine' mem_nhdsWithin_of_mem_nhds _
    rw [← mem_interior_iff_mem_nhds, interior_compl]
    exact disjoint_left.1 hd ha
  rcases exists_Icc_mem_subset_of_mem_nhdsWithin_Ici hmem with ⟨b, hab, hmem', hsub⟩
  -- ⊢ (ordConnectedSection (ordSeparatingSet s t))ᶜ ∈ 𝓝[Ici a] a
  by_cases H : Disjoint (Icc a b) (ordConnectedSection <| ordSeparatingSet s t)
  -- ⊢ (ordConnectedSection (ordSeparatingSet s t))ᶜ ∈ 𝓝[Ici a] a
  · exact mem_of_superset hmem' (disjoint_left.1 H)
    -- 🎉 no goals
  · simp only [Set.disjoint_left, not_forall, Classical.not_not] at H
    -- ⊢ (ordConnectedSection (ordSeparatingSet s t))ᶜ ∈ 𝓝[Ici a] a
    rcases H with ⟨c, ⟨hac, hcb⟩, hc⟩
    -- ⊢ (ordConnectedSection (ordSeparatingSet s t))ᶜ ∈ 𝓝[Ici a] a
    have hsub' : Icc a b ⊆ ordConnectedComponent tᶜ a :=
      subset_ordConnectedComponent (left_mem_Icc.2 hab) hsub
    have hd : Disjoint s (ordConnectedSection (ordSeparatingSet s t)) :=
      disjoint_left_ordSeparatingSet.mono_right ordConnectedSection_subset
    replace hac : a < c := hac.lt_of_ne <| Ne.symm <| ne_of_mem_of_not_mem hc <|
      disjoint_left.1 hd ha
    refine' mem_of_superset (Ico_mem_nhdsWithin_Ici (left_mem_Ico.2 hac)) fun x hx hx' => _
    -- ⊢ False
    refine' hx.2.ne (eq_of_mem_ordConnectedSection_of_uIcc_subset hx' hc _)
    -- ⊢ [[x, c]] ⊆ ordSeparatingSet s t
    refine' subset_inter (subset_iUnion₂_of_subset a ha _) _
    -- ⊢ [[x, c]] ⊆ ordConnectedComponent tᶜ a
    · exact OrdConnected.uIcc_subset inferInstance (hsub' ⟨hx.1, hx.2.le.trans hcb⟩)
        (hsub' ⟨hac.le, hcb⟩)
    · rcases mem_iUnion₂.1 (ordConnectedSection_subset hx').2 with ⟨y, hyt, hxy⟩
      -- ⊢ [[x, c]] ⊆ ⋃ (x : X) (_ : x ∈ t), ordConnectedComponent sᶜ x
      refine' subset_iUnion₂_of_subset y hyt (OrdConnected.uIcc_subset inferInstance hxy _)
      -- ⊢ c ∈ ordConnectedComponent sᶜ y
      refine' subset_ordConnectedComponent left_mem_uIcc hxy _
      -- ⊢ c ∈ [[y, x]]
      suffices c < y by
        rw [uIcc_of_ge (hx.2.trans this).le]
        exact ⟨hx.2.le, this.le⟩
      refine' lt_of_not_le fun hyc => _
      -- ⊢ False
      have hya : y < a := not_le.1 fun hay => hsub ⟨hay, hyc.trans hcb⟩ hyt
      -- ⊢ False
      exact hxy (Icc_subset_uIcc ⟨hya.le, hx.1⟩) ha
      -- 🎉 no goals
#align set.compl_section_ord_separating_set_mem_nhds_within_Ici Set.compl_section_ordSeparatingSet_mem_nhdsWithin_Ici

theorem compl_section_ordSeparatingSet_mem_nhdsWithin_Iic (hd : Disjoint s (closure t))
    (ha : a ∈ s) : (ordConnectedSection <| ordSeparatingSet s t)ᶜ ∈ 𝓝[≤] a := by
  have hd' : Disjoint (ofDual ⁻¹' s) (closure <| ofDual ⁻¹' t) := hd
  -- ⊢ (ordConnectedSection (ordSeparatingSet s t))ᶜ ∈ 𝓝[Iic a] a
  have ha' : toDual a ∈ ofDual ⁻¹' s := ha
  -- ⊢ (ordConnectedSection (ordSeparatingSet s t))ᶜ ∈ 𝓝[Iic a] a
  simpa only [dual_ordSeparatingSet, dual_ordConnectedSection] using
    compl_section_ordSeparatingSet_mem_nhdsWithin_Ici hd' ha'
#align set.compl_section_ord_separating_set_mem_nhds_within_Iic Set.compl_section_ordSeparatingSet_mem_nhdsWithin_Iic

theorem compl_section_ordSeparatingSet_mem_nhds (hd : Disjoint s (closure t)) (ha : a ∈ s) :
    (ordConnectedSection <| ordSeparatingSet s t)ᶜ ∈ 𝓝 a := by
  rw [← nhds_left_sup_nhds_right, mem_sup]
  -- ⊢ (ordConnectedSection (ordSeparatingSet s t))ᶜ ∈ 𝓝[Iic a] a ∧ (ordConnectedSe …
  exact
    ⟨compl_section_ordSeparatingSet_mem_nhdsWithin_Iic hd ha,
      compl_section_ordSeparatingSet_mem_nhdsWithin_Ici hd ha⟩
#align set.compl_section_ord_separating_set_mem_nhds Set.compl_section_ordSeparatingSet_mem_nhds

theorem ordT5Nhd_mem_nhdsSet (hd : Disjoint s (closure t)) : ordT5Nhd s t ∈ 𝓝ˢ s :=
  bUnion_mem_nhdsSet fun x hx => ordConnectedComponent_mem_nhds.2 <| inter_mem
    (by
      rw [← mem_interior_iff_mem_nhds, interior_compl]
      -- ⊢ x ∈ (closure t)ᶜ
      exact disjoint_left.1 hd hx)
      -- 🎉 no goals
    (compl_section_ordSeparatingSet_mem_nhds hd hx)
#align set.ord_t5_nhd_mem_nhds_set Set.ordT5Nhd_mem_nhdsSet

end Set

open Set

/-- A linear order with order topology is a completely normal Hausdorff topological space. -/
instance (priority := 100) OrderTopology.t5Space : T5Space X :=
  ⟨fun s t h₁ h₂ => Filter.disjoint_iff.2
    ⟨ordT5Nhd s t, ordT5Nhd_mem_nhdsSet h₂, ordT5Nhd t s, ordT5Nhd_mem_nhdsSet h₁.symm,
      disjoint_ordT5Nhd⟩⟩
#align order_topology.t5_space OrderTopology.t5Space
