/-
Copyright (c) 2026 Ben Eltschig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Eltschig
-/
module

public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! # The inclusion of the general linear group into linear maps is an open embedding

In this file we prove that for every finite-dimensional Hausdorff topological vector space `E`,
the inclusion of the general linear group `(E →L[𝕜] E)ˣ` into `E →L[𝕜] E` is an open embedding.
This is not trivial: the group of units `Mˣ` of a monoid `M` is generally equipped with the coarsest
topology making both `Units.val : Mˣ → X` and `Units.inv : Mˣ → M` continuous, so it only coincides
with the subspace topology here because inversion of continuous maps is already continuous away from
non-invertible maps.

The ingredients for this this (any finite-dimensional Hausdorff TVS is isomorphic to a
Banach space, `E →L[𝕜] E` is a Banach ring when `E` is a Banach space, every Banach ring satisfies
`IsOpenUnits`) already exist in various different files; we assemble them only here
to avoid adding imports to those other files.
-/

public section

/-- For any finite-dimensional Hausdorff topological vector space `E`, the general linear group
`(E →L[𝕜] E)ˣ` is open in `E →L[𝕜] E` and equipped with the subspace topology. -/
instance {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    {E : Type*} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul 𝕜 E] [T2Space E] [FiniteDimensional 𝕜 E] : IsOpenUnits (E →L[𝕜] E) :=
  ContinuousMulEquiv.isOpenUnits {
      ((Module.finBasis 𝕜 E).equivFunL.arrowCongr (Module.finBasis 𝕜 E).equivFunL).toHomeomorph with
    map_mul' := by intros; ext; simp }
