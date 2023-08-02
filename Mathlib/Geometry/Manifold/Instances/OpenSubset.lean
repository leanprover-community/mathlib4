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
  {hM : HasGroupoid M G} (U : Opens M) [Nonempty U]

/-- `U` is a `ChartedSpace` with the same model space as `M`. -/
instance open_sub_charted : ChartedSpace H U where
  atlas := {(HM.chartAt x).subtypeRestr U | x ∈ U}
  chartAt x := (HM.chartAt x).subtypeRestr U
  mem_chart_source x := by
    simp only [LocalHomeomorph.subtypeRestr_source, mem_preimage, mem_chart_source]
  chart_mem_atlas x := by
    use x
    simp

/-- `U` has an atlas in the same groupoid as `M`. -/
theorem open_sub_mfld : HasGroupoid U G where
  compatible := by
    intro e e' he he'
    simp only [atlas, ChartedSpace.atlas] at he he'
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
            rw [← he, ← he']
            apply LocalHomeomorph.subtypeRestr_symm_trans_subtypeRestr
