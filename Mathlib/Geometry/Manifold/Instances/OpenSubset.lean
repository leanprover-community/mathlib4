/-
Copyright (c) 2023 Michael Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Lee
-/
import Mathlib.Geometry.Manifold.SmoothManifoldWithCorners

/-!
# An open subset of a `C^k` manifold is a `C^k` manifold

We show that for manifold `M` which has the structure groupoid `G`, a nonempty open subset `U` of
`M` has manifold structure with the structure groupoid `G` that is equivalent to the one on `M`.
-/

noncomputable section

open Function Set TopologicalSpace

open scoped Manifold

variable {𝕜 : Type _} [NontriviallyNormedField 𝕜] {E : Type _} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type _} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) {M : Type _}
  [TopologicalSpace M] [HM : ChartedSpace H M] {G : StructureGroupoid H} [ClosedUnderRestriction G]
  {hM : HasGroupoid M G} (U : Opens M) [Nonempty U] (defPoint : U)

open Classical in
/-- This provides a one-to-one corresondence between the atlas on `M` and the atlas on `U`. -/
def restrChart (ch : LocalHomeomorph M H) : LocalHomeomorph U H where
  source := {x | x.val ∈ ch.source}
  target := ch.target ∩ (↑U ∩ ch.source).image ch.toFun
  toFun x := ch.toFun x
  invFun x := ⟨if x ∈ (↑U ∩ ch.source).image ch.toFun then ch.invFun x else defPoint, by
    split_ifs with h
    · rw [mem_image] at h
      cases h with
      | intro y hy =>
        rw [← hy.right]
        have hyin := (mem_inter_iff y U ch.source).mp hy.left
        exact (ch.left_inv' hyin.right).symm.subst hyin.left
    · exact SetLike.coe_mem defPoint
  ⟩
  map_source' := by
    simp only [Subtype.forall, Prod.forall, mem_inter_iff]
    intro a b ha
    apply And.intro (ch.map_source' ha) (mem_image_of_mem ch (mem_inter b ha))
  map_target' := by
    simp only [mem_inter_iff, mem_image, and_imp, forall_exists_index]
    intro x hx y hy hych hxy
    split_ifs with h
    · exact ch.map_target' hx
    · simp only [not_exists, not_and, and_imp] at h
      exact (h y hy hych hxy).elim
  left_inv' := by
    simp only [mem_inter_iff, Subtype.forall, Subtype.mk.injEq]
    intro a ha hach
    split_ifs with h
    · exact ch.left_inv' hach
    · simp only [mem_inter_iff, mem_image, not_exists, not_and, and_imp] at h
      exact (h a ha hach rfl).elim
  right_inv' := by
    simp only [mem_inter_iff, mem_image, and_imp, forall_exists_index]
    intro x hx y hy hych hxy
    split_ifs with h
    · exact ch.right_inv' hx
    · simp only [not_exists, not_and, and_imp] at h
      exact (h y hy hych hxy).elim
  open_source := by
    refine Iff.mpr isOpen_mk ?_
    use ch.source
    exact And.intro ch.open_source rfl
  open_target := ch.open_target.inter (ch.image_open_of_open (U.isOpen.inter ch.open_source)
    (inter_subset_right U ch.source))
  continuous_toFun := by
    simp only [LocalHomeomorph.toFun_eq_coe]
    apply ContinuousOn.comp
    · exact ch.continuous_toFun
    · exact continuous_id.subtype_val.continuousOn
    · simp [MapsTo]
  continuous_invFun := by
    apply continuousOn_iff'.mpr
    intro t ht
    use image ch.toFun (t.image Subtype.val ∩ ch.source)
    simp only []
    apply And.intro
    · exact (ch.image_open_of_open ((U.isOpen.isOpenMap_subtype_val t ht).inter ch.open_source)
        (inter_subset_right (t.image Subtype.val) ch.source))
    · apply ext
      simp only [mem_inter_iff, mem_preimage, mem_image, LocalHomeomorph.toFun_eq_coe,
        LocalEquiv.invFun_as_coe, LocalHomeomorph.coe_coe_symm, and_imp, and_congr_left_iff,
        forall_exists_index, exists_and_right, exists_eq_right, Subtype.exists]
      intro x _ y hy hych hxy
      simp_rw [← congrArg ch.symm hxy, ch.left_inv hych]
      apply Iff.intro
      · intro hx
        use y
        refine And.intro (And.intro ?_ hych) hxy
        use hy
        split_ifs at hx with hx1
        · exact hx
        · exact (hx1 (Exists.intro y ⟨⟨hy, hych⟩, hxy⟩)).elim
      · intro hx
        split_ifs with hx1
        · cases hx with
          | intro y1 hy1 => cases hy1.left.left with
            | intro hy2 hy3 =>
              rw [← hy1.right] at hxy
              have yy1 := congrArg ch.symm hxy
              rw [ch.left_inv hych, ch.left_inv hy1.left.right] at yy1
              simp_rw [yy1]
              exact hy3
        · exact (hx1 (Exists.intro y ⟨⟨hy, hych⟩, hxy⟩)).elim

/-- `U` is a `ChartedSpace` with the same model space as `M`. -/
instance open_sub_charted : ChartedSpace H U where
  atlas := {restrChart U defPoint ch | ch ∈ HM.atlas}
  chartAt x := restrChart U defPoint (HM.chartAt x)
  mem_chart_source x := by simp [restrChart]
  chart_mem_atlas x := by
    simp only [mem_setOf_eq]
    use HM.chartAt x
    simp

/-- `U` has an atlas in the same groupoid as `M`. -/
theorem open_sub_mfld : HasGroupoid U G where
  compatible := by
    intro e e' he he'
    simp only [atlas, ChartedSpace.atlas, iUnion_singleton_eq_range, mem_range,
      Subtype.exists] at he he'
    cases he with
    | intro x hx => cases hx with
      | intro hx he => cases he' with
        | intro x' hx' => cases hx' with
          | intro hx' he' =>
            have restr_mem := closedUnderRestriction'
              (hM.compatible (HM.chart_mem_atlas x) (HM.chart_mem_atlas x'))
              ((HM.chartAt x).preimage_open_of_open_symm U.isOpen)
            refine G.eq_on_source' (((HM.chartAt x).symm ≫ₕ HM.chartAt x').restr
              ((HM.chartAt x).target ∩ ((HM.chartAt x).symm ⁻¹' U))) (e.symm ≫ₕ e') restr_mem ?_
            rw [← he, ← he'];
            apply LocalHomeomorph.subtypeRestr_symm_trans_subtypeRestr
