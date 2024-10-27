/-
Copyright (c) 2024 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn
-/
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.UniqueDifferential
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

/-!
# Derivatives of maps in the tangent bundle

This file contains properties of derivatives which need the manifold structure of the tangent
bundle. Notably, it includes formulas for the tangent maps to charts, and unique differentiability
statements for subsets of the tangent bundle.
-/

open Bundle

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [SmoothManifoldWithCorners I M]

/-- The derivative of the chart at a base point is the chart of the tangent bundle, composed with
the identification between the tangent bundle of the model space and the product space. -/
theorem tangentMap_chart {p q : TangentBundle I M} (h : q.1 ∈ (chartAt H p.1).source) :
    tangentMap I I (chartAt H p.1) q =
      (TotalSpace.toProd _ _).symm
        ((chartAt (ModelProd H E) p : TangentBundle I M → ModelProd H E) q) := by
  dsimp [tangentMap]
  rw [MDifferentiableAt.mfderiv]
  · rfl
  · exact mdifferentiableAt_atlas (chart_mem_atlas _ _) h

/-- The derivative of the inverse of the chart at a base point is the inverse of the chart of the
tangent bundle, composed with the identification between the tangent bundle of the model space and
the product space. -/
theorem tangentMap_chart_symm {p : TangentBundle I M} {q : TangentBundle I H}
    (h : q.1 ∈ (chartAt H p.1).target) :
    tangentMap I I (chartAt H p.1).symm q =
      (chartAt (ModelProd H E) p).symm (TotalSpace.toProd H E q) := by
  dsimp only [tangentMap]
  rw [MDifferentiableAt.mfderiv (mdifferentiableAt_atlas_symm (chart_mem_atlas _ _) h)]
  simp only [ContinuousLinearMap.coe_coe, TangentBundle.chartAt, h, tangentBundleCore,
    mfld_simps, (· ∘ ·)]
  -- `simp` fails to apply `PartialEquiv.prod_symm` with `ModelProd`
  congr
  exact ((chartAt H (TotalSpace.proj p)).right_inv h).symm

lemma mfderiv_chartAt_eq_tangentCoordChange {x y : M} (hsrc : x ∈ (chartAt H y).source) :
    mfderiv I I (chartAt H y) x = tangentCoordChange I x y x := by
  have := mdifferentiableAt_atlas (I := I) (ChartedSpace.chart_mem_atlas _) hsrc
  simp [mfderiv, if_pos this, Function.comp_assoc]

/-- The preimage under the projection from the tangent bundle of a set with unique differential in
the basis also has unique differential. -/
theorem UniqueMDiffOn.tangentBundle_proj_preimage {s : Set M} (hs : UniqueMDiffOn I s) :
    UniqueMDiffOn I.tangent (π E (TangentSpace I) ⁻¹' s) :=
  hs.smooth_bundle_preimage _
