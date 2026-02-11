/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Sébastien Gouëzel, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# The derivative of bounded linear maps

For detailed documentation of the Fréchet derivative,
see the module docstring of `Mathlib/Analysis/Calculus/FDeriv/Basic.lean`.

This file contains the usual formulas (and existence assertions) for the derivative of
bounded linear maps.
-/

public section

open Asymptotics

namespace ContinuousLinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
variable {F : Type*} [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
variable (f : E →L[𝕜] F)
variable {x : E}
variable {s : Set E}
variable {L : Filter E}

/-!
### Bundled continuous linear maps

There are currently two variants of these in mathlib, the bundled version
(named `ContinuousLinearMap`, and denoted `E →L[𝕜] F`, works for topological vector spaces),
and the unbundled version (with a predicate `IsBoundedLinearMap`, requires normed spaces).
This section deals with the first form, see below for the unbundled version
-/

@[fun_prop]
protected theorem hasStrictFDerivAt : HasStrictFDerivAt f f x :=
  .of_isLittleOTVS <| (IsLittleOTVS.zero _ _).congr_left fun x => by
    simp only [f.map_sub, sub_self, Pi.zero_apply]

protected theorem hasFDerivAtFilter : HasFDerivAtFilter f f x L :=
  .of_isLittleOTVS <| (IsLittleOTVS.zero _ _).congr_left fun x => by
    simp only [f.map_sub, sub_self, Pi.zero_apply]

@[fun_prop]
protected theorem hasFDerivWithinAt : HasFDerivWithinAt f f s x :=
  f.hasFDerivAtFilter

@[fun_prop]
protected theorem hasFDerivAt : HasFDerivAt f f x :=
  f.hasFDerivAtFilter

@[simp, fun_prop]
protected theorem differentiableAt : DifferentiableAt 𝕜 f x :=
  f.hasFDerivAt.differentiableAt

@[fun_prop]
protected theorem differentiableWithinAt : DifferentiableWithinAt 𝕜 f s x :=
  f.differentiableAt.differentiableWithinAt

@[simp, fun_prop]
protected theorem differentiable : Differentiable 𝕜 f := fun _ =>
  f.differentiableAt

@[fun_prop]
protected theorem differentiableOn : DifferentiableOn 𝕜 f s :=
  f.differentiable.differentiableOn

variable [ContinuousAdd E] [ContinuousSMul 𝕜 E] [ContinuousAdd F] [ContinuousSMul 𝕜 F] [T2Space F]

@[simp]
protected theorem fderiv : fderiv 𝕜 f x = f :=
  f.hasFDerivAt.fderiv

protected theorem fderivWithin (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 f s x = f := by
  rw [DifferentiableAt.fderivWithin f.differentiableAt hxs]
  exact f.fderiv

end ContinuousLinearMap

/-! ### Unbundled continuous linear maps -/

namespace IsBoundedLinearMap
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {f : E → F}
variable {x : E}
variable {s : Set E}
variable {L : Filter E}

theorem hasFDerivAtFilter (h : IsBoundedLinearMap 𝕜 f) :
    HasFDerivAtFilter f h.toContinuousLinearMap x L :=
  h.toContinuousLinearMap.hasFDerivAtFilter

@[fun_prop]
theorem hasFDerivWithinAt (h : IsBoundedLinearMap 𝕜 f) :
    HasFDerivWithinAt f h.toContinuousLinearMap s x :=
  h.hasFDerivAtFilter

@[fun_prop]
theorem hasFDerivAt (h : IsBoundedLinearMap 𝕜 f) :
    HasFDerivAt f h.toContinuousLinearMap x :=
  h.hasFDerivAtFilter

@[fun_prop]
theorem differentiableAt (h : IsBoundedLinearMap 𝕜 f) : DifferentiableAt 𝕜 f x :=
  h.hasFDerivAt.differentiableAt

@[fun_prop]
theorem differentiableWithinAt (h : IsBoundedLinearMap 𝕜 f) :
    DifferentiableWithinAt 𝕜 f s x :=
  h.differentiableAt.differentiableWithinAt

protected theorem fderiv (h : IsBoundedLinearMap 𝕜 f) :
    fderiv 𝕜 f x = h.toContinuousLinearMap :=
  HasFDerivAt.fderiv h.hasFDerivAt

protected theorem fderivWithin (h : IsBoundedLinearMap 𝕜 f)
    (hxs : UniqueDiffWithinAt 𝕜 s x) : fderivWithin 𝕜 f s x = h.toContinuousLinearMap := by
  rw [DifferentiableAt.fderivWithin h.differentiableAt hxs]
  exact h.fderiv

@[fun_prop]
theorem differentiable (h : IsBoundedLinearMap 𝕜 f) : Differentiable 𝕜 f :=
  fun _ => h.differentiableAt

@[fun_prop]
theorem differentiableOn (h : IsBoundedLinearMap 𝕜 f) : DifferentiableOn 𝕜 f s :=
  h.differentiable.differentiableOn

end IsBoundedLinearMap
