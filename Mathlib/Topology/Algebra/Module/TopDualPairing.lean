/-
Copyright (c) 2025 Bjørn Solheim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Solheim
-/
module

public import Mathlib.Topology.Algebra.Module.PerfectPairing
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import Mathlib.Algebra.EuclideanDomain.Field
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Init
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.Module.FiniteDimension

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
