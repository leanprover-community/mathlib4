/-
Copyright (c) 2022 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

/-!
# Manifold structure on the upper half plane.

In this file we define the complex manifold structure on the upper half-plane.
-/

open Filter

open scoped Manifold

namespace UpperHalfPlane

noncomputable instance : ChartedSpace ℂ ℍ :=
  UpperHalfPlane.isOpenEmbedding_coe.singletonChartedSpace

instance : SmoothManifoldWithCorners 𝓘(ℂ) ℍ :=
  UpperHalfPlane.isOpenEmbedding_coe.singleton_smoothManifoldWithCorners 𝓘(ℂ)

/-- The inclusion map `ℍ → ℂ` is a smooth map of manifolds. -/
theorem smooth_coe : Smooth 𝓘(ℂ) 𝓘(ℂ) ((↑) : ℍ → ℂ) := fun _ => contMDiffAt_extChartAt

/-- The inclusion map `ℍ → ℂ` is a differentiable map of manifolds. -/
theorem mdifferentiable_coe : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) ((↑) : ℍ → ℂ) :=
  smooth_coe.mdifferentiable

lemma smoothAt_ofComplex {z : ℂ} (hz : 0 < z.im) :
    SmoothAt 𝓘(ℂ) 𝓘(ℂ) ofComplex z := by
  rw [SmoothAt, contMDiffAt_iff]
  constructor
  · -- continuity at z
    rw [ContinuousAt, nhds_induced, tendsto_comap_iff]
    refine Tendsto.congr' (eventuallyEq_coe_comp_ofComplex hz).symm ?_
    simpa only [ofComplex_apply_of_im_pos hz, Subtype.coe_mk] using tendsto_id
  · -- smoothness in local chart
    simp only [extChartAt, PartialHomeomorph.extend, IsOpenEmbedding.toPartialHomeomorph_source,
      PartialHomeomorph.singletonChartedSpace_chartAt_eq, modelWithCornersSelf_partialEquiv,
      PartialEquiv.trans_refl, PartialHomeomorph.toFun_eq_coe,
      IsOpenEmbedding.toPartialHomeomorph_apply, PartialHomeomorph.refl_partialEquiv,
      PartialEquiv.refl_source, PartialEquiv.refl_symm, PartialEquiv.refl_coe, CompTriple.comp_eq,
      modelWithCornersSelf_coe, Set.range_id, id_eq, contDiffWithinAt_univ]
    exact contDiffAt_id.congr_of_eventuallyEq (eventuallyEq_coe_comp_ofComplex hz)

lemma mdifferentiableAt_ofComplex {z : ℂ} (hz : 0 < z.im) :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) ofComplex z :=
  (smoothAt_ofComplex hz).mdifferentiableAt

lemma mdifferentiableAt_iff {f : ℍ → ℂ} {τ : ℍ} :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f τ ↔ DifferentiableAt ℂ (f ∘ ofComplex) ↑τ := by
  rw [← mdifferentiableAt_iff_differentiableAt]
  refine ⟨fun hf ↦ ?_, fun hf ↦ ?_⟩
  · exact (ofComplex_apply τ ▸ hf).comp _ (mdifferentiableAt_ofComplex τ.im_pos)
  · simpa only [Function.comp_def, ofComplex_apply] using hf.comp τ (mdifferentiable_coe τ)

end UpperHalfPlane
