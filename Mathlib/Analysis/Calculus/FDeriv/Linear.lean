/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Sébastien Gouëzel, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Calculus.TangentCone.Defs
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Calculus.FDeriv.Basic

/-!
# The derivative of bounded linear maps

For detailed documentation of the Fréchet derivative,
see the module docstring of `Mathlib/Analysis/Calculus/FDeriv/Basic.lean`.

This file contains the usual formulas (and existence assertions)
for the derivative of continuous linear maps, both bundled and unbundled.

We also prove versions of the chain rule when one of the map is a continuous linear map,
whenever they can be proved with fewer typeclass assumptions than the general chain rules.
-/

public section

open Asymptotics

namespace ContinuousLinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
variable {F : Type*} [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]

/-!
### Bundled continuous linear maps

There are currently two variants of these in mathlib, the bundled version
(named `ContinuousLinearMap`, and denoted `E →L[𝕜] F`, works for topological vector spaces),
and the unbundled version (with a predicate `IsBoundedLinearMap`, requires normed spaces).
This section deals with the first form, see below for the unbundled version
-/

section Basic
variable (f : E →L[𝕜] F) {x : E} {s : Set E} {L : Filter E}

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

end Basic

variable {G : Type*} [AddCommGroup G] [Module 𝕜 G] [TopologicalSpace G]

/-!
### Chain rule for continuous linear maps

The chain rule says that given two differentiable functions `g` and `f`,
the function `g ∘ f` is differentiable too, with derivative `g' ∘L f'`.

In the context of topological vector spaces,
the chain rule needs all 3 spaces to be TVS, not just vector spaces with topology.
It means that the addition and scalar multiplication need to be continuous.
While we do not actually care about derivatives on non-TVS vector spaces with topology,
the theorems below allow us to save a few typeclass instance searches
compared to the generic chain rule.
-/

section CompLeft
variable (g : F →L[𝕜] G) {f : E → F} {f' : E →L[𝕜] F} {s : Set E} {x : E} {L : Filter E}

theorem comp_hasFDerivAtFilter (hf : HasFDerivAtFilter f f' x L) :
    HasFDerivAtFilter (g ∘ f) (g ∘L f') x L :=
  .of_isLittleOTVS <| by
    simpa [Function.comp_def] using g.isBigOTVS_comp.trans_isLittleOTVS hf.isLittleOTVS

theorem comp_hasStrictFDerivAt (hf : HasStrictFDerivAt f f' x) :
    HasStrictFDerivAt (g ∘ f) (g ∘L f') x :=
  .of_isLittleOTVS <| by
    simpa [Function.comp_def] using g.isBigOTVS_comp.trans_isLittleOTVS hf.isLittleOTVS

theorem comp_hasFDerivAt (hf : HasFDerivAt f f' x) : HasFDerivAt (g ∘ f) (g ∘L f') x :=
  g.comp_hasFDerivAtFilter hf

theorem comp_hasFDerivWithinAt (hf : HasFDerivWithinAt f f' s x) :
    HasFDerivWithinAt (g ∘ f) (g ∘L f') s x :=
  g.comp_hasFDerivAtFilter hf

theorem comp_differentiableWithinAt (hf : DifferentiableWithinAt 𝕜 f s x) :
    DifferentiableWithinAt 𝕜 (g ∘ f) s x :=
  g.comp_hasFDerivWithinAt hf.hasFDerivWithinAt |>.differentiableWithinAt

theorem comp_differentiableOn (hf : DifferentiableOn 𝕜 f s) : DifferentiableOn 𝕜 (g ∘ f) s :=
  fun x hx ↦ g.comp_differentiableWithinAt (hf x hx)

theorem comp_differentiableAt (hf : DifferentiableAt 𝕜 f x) : DifferentiableAt 𝕜 (g ∘ f) x :=
  g.comp_hasFDerivAt hf.hasFDerivAt |>.differentiableAt

theorem comp_differentiable (hf : Differentiable 𝕜 f) : Differentiable 𝕜 (g ∘ f) :=
  fun x ↦ g.comp_differentiableAt (hf x)

variable [ContinuousAdd E] [ContinuousSMul 𝕜 E] [ContinuousAdd G] [ContinuousSMul 𝕜 G] [T2Space G]

theorem fderiv_comp_left (hf : DifferentiableAt 𝕜 f x) : fderiv 𝕜 (g ∘ f) x = g ∘L fderiv 𝕜 f x :=
  g.comp_hasFDerivAt hf.hasFDerivAt |>.fderiv

theorem fderivWithin_comp_left (hf : DifferentiableWithinAt 𝕜 f s x)
    (hs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (g ∘ f) s x = g ∘L fderivWithin 𝕜 f s x :=
  g.comp_hasFDerivWithinAt hf.hasFDerivWithinAt |>.fderivWithin hs

end CompLeft

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
