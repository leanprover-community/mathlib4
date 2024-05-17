/-
Copyright (c) 2022 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
import Mathlib.Geometry.Manifold.MFDeriv.Basic

#align_import analysis.complex.upper_half_plane.manifold from "leanprover-community/mathlib"@"57f9349f2fe19d2de7207e99b0341808d977cdcf"

/-!
# Manifold structure on the upper half plane.

In this file we define the complex manifold structure on the upper half-plane.
-/

open Set Filter PartialHomeomorph

open scoped UpperHalfPlane Manifold Topology

namespace UpperHalfPlane

noncomputable instance : ChartedSpace ℂ ℍ :=
  UpperHalfPlane.openEmbedding_coe.singletonChartedSpace

instance : SmoothManifoldWithCorners 𝓘(ℂ) ℍ :=
  UpperHalfPlane.openEmbedding_coe.singleton_smoothManifoldWithCorners 𝓘(ℂ)

/-- The inclusion map `ℍ → ℂ` is a smooth map of manifolds. -/
theorem smooth_coe : Smooth 𝓘(ℂ) 𝓘(ℂ) ((↑) : ℍ → ℂ) := fun _ => contMDiffAt_extChartAt
#align upper_half_plane.smooth_coe UpperHalfPlane.smooth_coe

/-- The inclusion map `ℍ → ℂ` is a differentiable map of manifolds. -/
theorem mdifferentiable_coe : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) ((↑) : ℍ → ℂ) :=
  smooth_coe.mdifferentiable
#align upper_half_plane.mdifferentiable_coe UpperHalfPlane.mdifferentiable_coe

local notation "↑ₕ" f => f ∘ (PartialHomeomorph.symm
          (OpenEmbedding.toPartialHomeomorph UpperHalfPlane.coe openEmbedding_coe))

/--This shows that being MDifferentiable as a map `ℍ → ℂ` is equivalent to being
differentiable on `{z : ℂ | 0 < z.im}` after arbitrarily extending to a function on all of `ℂ`.-/
lemma MDifferentiable_iff_extension_DifferentiableOn (f : ℍ → ℂ) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f ↔
    DifferentiableOn ℂ (↑ₕf) (UpperHalfPlane.coe '' ⊤) := by
  rw [_root_.MDifferentiable]
  constructor
  · intro h z hz
    obtain ⟨y, _, hy⟩ := hz
    have H := h y
    rw [mdifferentiableAt_iff] at H
    simp only [top_eq_univ, mem_univ, ← hy, writtenInExtChartAt, extChartAt, extend,
      refl_partialEquiv, PartialEquiv.refl_source, singletonChartedSpace_chartAt_eq,
      modelWithCornersSelf_partialEquiv, PartialEquiv.trans_refl, PartialEquiv.refl_coe,
      OpenEmbedding.toPartialHomeomorph_source, coe_coe_symm, CompTriple.comp_eq,
      modelWithCornersSelf_coe, range_id, toFun_eq_coe, OpenEmbedding.toPartialHomeomorph_apply,
      image_univ] at *
    apply H.2.mono (Set.subset_univ _)
  · intro h z
    have ha : UpperHalfPlane.coe '' ⊤ ∈ 𝓝 ↑z := by
      exact IsOpenMap.image_mem_nhds (OpenEmbedding.isOpenMap openEmbedding_coe)
        (by simp only [top_eq_univ, univ_mem])
    constructor
    · rw [continuousWithinAt_univ, continuousAt_iff_continuousAt_comp_right
        (e := (PartialHomeomorph.symm (OpenEmbedding.toPartialHomeomorph
        UpperHalfPlane.coe openEmbedding_coe)))]
      · exact ContinuousOn.continuousAt (h.continuousOn) ha
      · simp only [symm_toPartialEquiv, PartialEquiv.symm_target,
        OpenEmbedding.toPartialHomeomorph_source, mem_univ]
    · simp only [DifferentiableWithinAtProp, modelWithCornersSelf_coe, refl_partialEquiv,
      PartialEquiv.refl_source, singletonChartedSpace_chartAt_eq, refl_apply,
      OpenEmbedding.toPartialHomeomorph_source, CompTriple.comp_eq, modelWithCornersSelf_coe_symm,
      preimage_univ, range_id, inter_self, OpenEmbedding.toPartialHomeomorph_apply, id_eq,
      differentiableWithinAt_univ]
      exact DifferentiableOn.differentiableAt h ha

end UpperHalfPlane
