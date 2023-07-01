/-
Copyright (c) 2022 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck

! This file was ported from Lean 3 source module analysis.complex.upper_half_plane.manifold
! leanprover-community/mathlib commit 57f9349f2fe19d2de7207e99b0341808d977cdcf
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
import Mathlib.Geometry.Manifold.ContMdiffMfderiv

/-!
# Manifold structure on the upper half plane.

In this file we define the complex manifold structure on the upper half-plane.
-/


open scoped UpperHalfPlane Manifold

namespace UpperHalfPlane

noncomputable instance : ChartedSpace ℂ ℍ :=
  UpperHalfPlane.openEmbedding_coe.singletonChartedSpace

instance : SmoothManifoldWithCorners 𝓘(ℂ) ℍ :=
  UpperHalfPlane.openEmbedding_coe.singleton_smoothManifoldWithCorners 𝓘(ℂ)

/-- The inclusion map `ℍ → ℂ` is a smooth map of manifolds. -/
theorem smooth_coe : Smooth 𝓘(ℂ) 𝓘(ℂ) (coe : ℍ → ℂ) := fun x => contMDiffAt_extChartAt
#align upper_half_plane.smooth_coe UpperHalfPlane.smooth_coe

/-- The inclusion map `ℍ → ℂ` is a differentiable map of manifolds. -/
theorem mDifferentiable_coe : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (coe : ℍ → ℂ) :=
  smooth_coe.MDifferentiable
#align upper_half_plane.mdifferentiable_coe UpperHalfPlane.mDifferentiable_coe

end UpperHalfPlane

