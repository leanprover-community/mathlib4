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


/-- Extend a function on `ℍ` arbitrarily to a function on all of `ℂ`. -/
scoped[UpperHalfPlane] notation "↑ₕ" f => f ∘ (PartialHomeomorph.symm
          (OpenEmbedding.toPartialHomeomorph UpperHalfPlane.coe openEmbedding_coe))

lemma extends_def (f : ℍ → ℂ) (z : ℍ) :
    (↑ₕ f) z.1 = f z := by
  have := PartialHomeomorph.left_inv (PartialHomeomorph.symm
    (OpenEmbedding.toPartialHomeomorph UpperHalfPlane.coe openEmbedding_coe)) (x := z.1) ?_
  · simp only [Function.comp_apply]
    congr 1
    ext
    simpa only [PartialHomeomorph.symm_symm, OpenEmbedding.toPartialHomeomorph_apply,
      UpperHalfPlane.coe] using this
  · simp only [PartialHomeomorph.symm_toPartialEquiv, PartialEquiv.symm_source,
       OpenEmbedding.toPartialHomeomorph_target, mem_range]
    exists z

end UpperHalfPlane
