/-
Copyright (c) 2019 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Linear

/-!
# Derivatives of continuous linear maps from the base field

In this file we prove that `f : 𝕜 →L[𝕜] E` (or `f : 𝕜 →ₗ[𝕜] E`) has derivative `f 1`.

For a more detailed overview of one-dimensional derivatives in mathlib, see the module docstring of
`Analysis/Calculus/Deriv/Basic`.

## Keywords

derivative, linear map
-/
set_option backward.defeqAttrib.useBackward true

public section


universe u v w

open Topology Filter

open Filter Asymptotics Set

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {E : Type w} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {x : 𝕜}
variable {s : Set 𝕜}
variable {L : Filter (𝕜 × 𝕜)}

section ContinuousLinearMap

/-! ### Derivative of continuous linear maps -/

variable (e : 𝕜 →L[𝕜] F)

protected theorem ContinuousLinearMap.hasDerivAtFilter : HasDerivAtFilter e (e 1) L :=
  e.hasFDerivAtFilter.hasDerivAtFilter

protected theorem ContinuousLinearMap.hasStrictDerivAt : HasStrictDerivAt e (e 1) x :=
  e.hasDerivAtFilter

protected theorem ContinuousLinearMap.hasDerivAt : HasDerivAt e (e 1) x :=
  e.hasDerivAtFilter

protected theorem ContinuousLinearMap.hasDerivWithinAt : HasDerivWithinAt e (e 1) s x :=
  e.hasDerivAtFilter

@[simp]
protected theorem ContinuousLinearMap.deriv : deriv e x = e 1 :=
  e.hasDerivAt.deriv

protected theorem ContinuousLinearMap.derivWithin (hxs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin e s x = e 1 :=
  e.hasDerivWithinAt.derivWithin hxs

end ContinuousLinearMap

section LinearMap

/-! ### Derivative of bundled linear maps -/

variable (e : 𝕜 →ₗ[𝕜] F)

protected theorem LinearMap.hasDerivAtFilter : HasDerivAtFilter e (e 1) L :=
  e.toContinuousLinearMap₁.hasDerivAtFilter

protected theorem LinearMap.hasStrictDerivAt : HasStrictDerivAt e (e 1) x :=
  e.hasDerivAtFilter

protected theorem LinearMap.hasDerivAt : HasDerivAt e (e 1) x :=
  e.hasDerivAtFilter

protected theorem LinearMap.hasDerivWithinAt : HasDerivWithinAt e (e 1) s x :=
  e.hasDerivAtFilter

@[simp]
protected theorem LinearMap.deriv : deriv e x = e 1 :=
  e.hasDerivAt.deriv

protected theorem LinearMap.derivWithin (hxs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin e s x = e 1 :=
  e.hasDerivWithinAt.derivWithin hxs

end LinearMap
