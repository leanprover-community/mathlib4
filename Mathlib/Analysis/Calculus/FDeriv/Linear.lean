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

open Topology Classical NNReal Filter Asymptotics ENNReal

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


protected theorem ContinuousLinearMap.hasStrictFDerivAt {x : E} : HasStrictFDerivAt e e x :=
  (isLittleO_zero _ _).congr_left fun x => by simp only [e.map_sub, sub_self]

protected theorem ContinuousLinearMap.hasFDerivAtFilter : HasFDerivAtFilter e e x L :=
  (isLittleO_zero _ _).congr_left fun x => by simp only [e.map_sub, sub_self]

protected theorem ContinuousLinearMap.hasFDerivWithinAt : HasFDerivWithinAt e e s x :=
  e.hasFDerivAtFilter

protected theorem ContinuousLinearMap.hasFDerivAt : HasFDerivAt e e x :=
  e.hasFDerivAtFilter

@[simp]
protected theorem ContinuousLinearMap.differentiableAt : DifferentiableAt 𝕜 e x :=
  e.hasFDerivAt.differentiableAt

protected theorem ContinuousLinearMap.differentiableWithinAt : DifferentiableWithinAt 𝕜 e s x :=
  e.differentiableAt.differentiableWithinAt

@[simp]
protected theorem ContinuousLinearMap.fderiv : fderiv 𝕜 e x = e :=
  e.hasFDerivAt.fderiv

protected theorem ContinuousLinearMap.fderivWithin (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 e s x = e := by
  rw [DifferentiableAt.fderivWithin e.differentiableAt hxs]
  exact e.fderiv

@[simp]
protected theorem ContinuousLinearMap.differentiable : Differentiable 𝕜 e := fun _ =>
  e.differentiableAt

protected theorem ContinuousLinearMap.differentiableOn : DifferentiableOn 𝕜 e s :=
  e.differentiable.differentiableOn

theorem IsBoundedLinearMap.hasFDerivAtFilter (h : IsBoundedLinearMap 𝕜 f) :
    HasFDerivAtFilter f h.toContinuousLinearMap x L :=
  h.toContinuousLinearMap.hasFDerivAtFilter

theorem IsBoundedLinearMap.hasFDerivWithinAt (h : IsBoundedLinearMap 𝕜 f) :
    HasFDerivWithinAt f h.toContinuousLinearMap s x :=
  h.hasFDerivAtFilter

theorem IsBoundedLinearMap.hasFDerivAt (h : IsBoundedLinearMap 𝕜 f) :
    HasFDerivAt f h.toContinuousLinearMap x :=
  h.hasFDerivAtFilter

theorem IsBoundedLinearMap.differentiableAt (h : IsBoundedLinearMap 𝕜 f) : DifferentiableAt 𝕜 f x :=
  h.hasFDerivAt.differentiableAt

theorem IsBoundedLinearMap.differentiableWithinAt (h : IsBoundedLinearMap 𝕜 f) :
    DifferentiableWithinAt 𝕜 f s x :=
  h.differentiableAt.differentiableWithinAt

theorem IsBoundedLinearMap.fderiv (h : IsBoundedLinearMap 𝕜 f) :
    fderiv 𝕜 f x = h.toContinuousLinearMap :=
  HasFDerivAt.fderiv h.hasFDerivAt

theorem IsBoundedLinearMap.fderivWithin (h : IsBoundedLinearMap 𝕜 f)
    (hxs : UniqueDiffWithinAt 𝕜 s x) : fderivWithin 𝕜 f s x = h.toContinuousLinearMap := by
  rw [DifferentiableAt.fderivWithin h.differentiableAt hxs]
  exact h.fderiv

theorem IsBoundedLinearMap.differentiable (h : IsBoundedLinearMap 𝕜 f) : Differentiable 𝕜 f :=
  fun _ => h.differentiableAt

theorem IsBoundedLinearMap.differentiableOn (h : IsBoundedLinearMap 𝕜 f) : DifferentiableOn 𝕜 f s :=
  h.differentiable.differentiableOn

end ContinuousLinearMap

end
