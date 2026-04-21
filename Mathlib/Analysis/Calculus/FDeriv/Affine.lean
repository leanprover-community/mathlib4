/-
Copyright (c) 2025 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Topology.Algebra.ContinuousAffineMap


/-!
# The derivative of continuous affine maps

For detailed documentation of the Fréchet derivative,
see the module docstring of `Mathlib/Analysis/Calculus/FDeriv/Basic.lean`.

This file contains the usual formulas (and existence assertions) for the derivative of
continuous affine maps.
-/
set_option backward.defeqAttrib.useBackward true

public section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  (f : E →ᴬ[𝕜] F) {x : E} {s : Set E} {L : Filter (E × E)}

namespace ContinuousAffineMap

/-!
### Continuous affine maps
-/

protected theorem hasFDerivAtFilter : HasFDerivAtFilter f f.contLinear L := by
  refine .of_isLittleOTVS <| .congr_left (.zero _ _) ?_
  simp [(vsub_eq_sub _ _).symm.trans (f.contLinear_map_vsub _ _).symm]

@[fun_prop]
protected theorem hasStrictFDerivAt {x : E} : HasStrictFDerivAt f f.contLinear x :=
  f.hasFDerivAtFilter

@[fun_prop]
protected theorem hasFDerivWithinAt : HasFDerivWithinAt f f.contLinear s x :=
  f.hasFDerivAtFilter

@[fun_prop]
protected theorem hasFDerivAt : HasFDerivAt f f.contLinear x :=
  f.hasFDerivAtFilter

@[simp, fun_prop]
protected theorem differentiableAt : DifferentiableAt 𝕜 f x :=
  f.hasFDerivAt.differentiableAt

@[fun_prop]
protected theorem differentiableWithinAt : DifferentiableWithinAt 𝕜 f s x :=
  f.differentiableAt.differentiableWithinAt

@[simp]
protected theorem fderiv : fderiv 𝕜 f x = f.contLinear :=
  f.hasFDerivAt.fderiv

protected theorem fderivWithin (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 f s x = f.contLinear := by
  rw [DifferentiableAt.fderivWithin f.differentiableAt hxs]
  exact f.fderiv

@[simp, fun_prop]
protected theorem differentiable : Differentiable 𝕜 f := fun _ =>
  f.differentiableAt

@[fun_prop]
protected theorem differentiableOn : DifferentiableOn 𝕜 f s :=
  f.differentiable.differentiableOn

end ContinuousAffineMap
