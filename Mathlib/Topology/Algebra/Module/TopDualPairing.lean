/-
Copyright (c) 2025 Bjørn Solheim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Solheim
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Module.PerfectPairing
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-!
# Continuous Perfect Pairing for `topDualPairing`

This file proves that `topDualPairing 𝕜 E` is a continuous perfect pairing when `E` is a
finite-dimensional Hausdorff space over a complete nontrivially normed field.

## Main results

* `topDualPairing_isContPerfPair`: The `topDualPairing` is a continuous perfect pairing for
  finite-dimensional Hausdorff spaces over complete nontrivially normed fields.
-/

@[expose] public section

open Module

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type*} [AddCommGroup E] [Module 𝕜 E]
variable [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
variable [FiniteDimensional 𝕜 E] [T2Space E]

/-- The `topDualPairing` is a continuous perfect pairing for finite-dimensional
Hausdorff spaces over complete nontrivially normed fields. -/
instance topDualPairing_isContPerfPair : (topDualPairing 𝕜 E).IsContPerfPair where
  continuous_uncurry := by
    haveI : IsModuleTopology 𝕜 E := isModuleTopologyOfFiniteDimensional
    haveI : IsModuleTopology 𝕜 (E →L[𝕜] 𝕜) := isModuleTopologyOfFiniteDimensional
    exact IsModuleTopology.continuous_bilinear_of_finite_left (topDualPairing 𝕜 E)
  bijective_left := Function.bijective_id
  bijective_right := by
    refine LinearMap.toContinuousLinearMap.bijective.comp ?_
    rw [LinearMap.flip_bijective_iff₁]
    exact LinearMap.toContinuousLinearMap.symm.bijective
