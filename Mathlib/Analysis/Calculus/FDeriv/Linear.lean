/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Sébastien Gouëzel, Yury Kudryashov
-/
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.NormedSpace.BoundedLinearMaps

#align_import analysis.calculus.fderiv.linear from "leanprover-community/mathlib"@"e3fb84046afd187b710170887195d50bada934ee"

/-!
# The derivative of bounded linear maps

For detailed documentation of the Fréchet derivative,
see the module docstring of `Analysis/Calculus/FDeriv/Basic.lean`.

This file contains the usual formulas (and existence assertions) for the derivative of
bounded linear maps.
-/


open Filter Asymptotics ContinuousLinearMap Set Metric

open scoped Classical
open Topology NNReal Filter Asymptotics ENNReal

noncomputable section

section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
variable {G' : Type*} [NormedAddCommGroup G'] [NormedSpace 𝕜 G']
variable {f f₀ f₁ g : E → F}
variable {f' f₀' f₁' g' : E →L[𝕜] F}
variable (e : E →L[𝕜] F)
variable {x : E}
variable {s t : Set E}
variable {L L₁ L₂ : Filter E}

section ContinuousLinearMap

/-!
### Continuous linear maps

There are currently two variants of these in mathlib, the bundled version
(named `ContinuousLinearMap`, and denoted `E →L[𝕜] F`), and the unbundled version (with a
predicate `IsBoundedLinearMap`). We give statements for both versions. -/


@[fun_prop]
protected theorem ContinuousLinearMap.hasStrictFDerivAt {x : E} : HasStrictFDerivAt e e x :=
  (isLittleO_zero _ _).congr_left fun x => by simp only [e.map_sub, sub_self]
#align continuous_linear_map.has_strict_fderiv_at ContinuousLinearMap.hasStrictFDerivAt

protected theorem ContinuousLinearMap.hasFDerivAtFilter : HasFDerivAtFilter e e x L :=
  .of_isLittleO <| (isLittleO_zero _ _).congr_left fun x => by simp only [e.map_sub, sub_self]
#align continuous_linear_map.has_fderiv_at_filter ContinuousLinearMap.hasFDerivAtFilter

@[fun_prop]
protected theorem ContinuousLinearMap.hasFDerivWithinAt : HasFDerivWithinAt e e s x :=
  e.hasFDerivAtFilter
#align continuous_linear_map.has_fderiv_within_at ContinuousLinearMap.hasFDerivWithinAt

@[fun_prop]
protected theorem ContinuousLinearMap.hasFDerivAt : HasFDerivAt e e x :=
  e.hasFDerivAtFilter
#align continuous_linear_map.has_fderiv_at ContinuousLinearMap.hasFDerivAt

@[simp, fun_prop]
protected theorem ContinuousLinearMap.differentiableAt : DifferentiableAt 𝕜 e x :=
  e.hasFDerivAt.differentiableAt
#align continuous_linear_map.differentiable_at ContinuousLinearMap.differentiableAt

@[fun_prop]
protected theorem ContinuousLinearMap.differentiableWithinAt : DifferentiableWithinAt 𝕜 e s x :=
  e.differentiableAt.differentiableWithinAt
#align continuous_linear_map.differentiable_within_at ContinuousLinearMap.differentiableWithinAt

@[simp]
protected theorem ContinuousLinearMap.fderiv : fderiv 𝕜 e x = e :=
  e.hasFDerivAt.fderiv
#align continuous_linear_map.fderiv ContinuousLinearMap.fderiv

protected theorem ContinuousLinearMap.fderivWithin (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 e s x = e := by
  rw [DifferentiableAt.fderivWithin e.differentiableAt hxs]
  exact e.fderiv
#align continuous_linear_map.fderiv_within ContinuousLinearMap.fderivWithin

@[simp, fun_prop]
protected theorem ContinuousLinearMap.differentiable : Differentiable 𝕜 e := fun _ =>
  e.differentiableAt
#align continuous_linear_map.differentiable ContinuousLinearMap.differentiable

@[fun_prop]
protected theorem ContinuousLinearMap.differentiableOn : DifferentiableOn 𝕜 e s :=
  e.differentiable.differentiableOn
#align continuous_linear_map.differentiable_on ContinuousLinearMap.differentiableOn

theorem IsBoundedLinearMap.hasFDerivAtFilter (h : IsBoundedLinearMap 𝕜 f) :
    HasFDerivAtFilter f h.toContinuousLinearMap x L :=
  h.toContinuousLinearMap.hasFDerivAtFilter
#align is_bounded_linear_map.has_fderiv_at_filter IsBoundedLinearMap.hasFDerivAtFilter

@[fun_prop]
theorem IsBoundedLinearMap.hasFDerivWithinAt (h : IsBoundedLinearMap 𝕜 f) :
    HasFDerivWithinAt f h.toContinuousLinearMap s x :=
  h.hasFDerivAtFilter
#align is_bounded_linear_map.has_fderiv_within_at IsBoundedLinearMap.hasFDerivWithinAt

@[fun_prop]
theorem IsBoundedLinearMap.hasFDerivAt (h : IsBoundedLinearMap 𝕜 f) :
    HasFDerivAt f h.toContinuousLinearMap x :=
  h.hasFDerivAtFilter
#align is_bounded_linear_map.has_fderiv_at IsBoundedLinearMap.hasFDerivAt

@[fun_prop]
theorem IsBoundedLinearMap.differentiableAt (h : IsBoundedLinearMap 𝕜 f) : DifferentiableAt 𝕜 f x :=
  h.hasFDerivAt.differentiableAt
#align is_bounded_linear_map.differentiable_at IsBoundedLinearMap.differentiableAt

@[fun_prop]
theorem IsBoundedLinearMap.differentiableWithinAt (h : IsBoundedLinearMap 𝕜 f) :
    DifferentiableWithinAt 𝕜 f s x :=
  h.differentiableAt.differentiableWithinAt
#align is_bounded_linear_map.differentiable_within_at IsBoundedLinearMap.differentiableWithinAt

theorem IsBoundedLinearMap.fderiv (h : IsBoundedLinearMap 𝕜 f) :
    fderiv 𝕜 f x = h.toContinuousLinearMap :=
  HasFDerivAt.fderiv h.hasFDerivAt
#align is_bounded_linear_map.fderiv IsBoundedLinearMap.fderiv

theorem IsBoundedLinearMap.fderivWithin (h : IsBoundedLinearMap 𝕜 f)
    (hxs : UniqueDiffWithinAt 𝕜 s x) : fderivWithin 𝕜 f s x = h.toContinuousLinearMap := by
  rw [DifferentiableAt.fderivWithin h.differentiableAt hxs]
  exact h.fderiv
#align is_bounded_linear_map.fderiv_within IsBoundedLinearMap.fderivWithin

@[fun_prop]
theorem IsBoundedLinearMap.differentiable (h : IsBoundedLinearMap 𝕜 f) : Differentiable 𝕜 f :=
  fun _ => h.differentiableAt
#align is_bounded_linear_map.differentiable IsBoundedLinearMap.differentiable

@[fun_prop]
theorem IsBoundedLinearMap.differentiableOn (h : IsBoundedLinearMap 𝕜 f) : DifferentiableOn 𝕜 f s :=
  h.differentiable.differentiableOn
#align is_bounded_linear_map.differentiable_on IsBoundedLinearMap.differentiableOn

end ContinuousLinearMap

end
