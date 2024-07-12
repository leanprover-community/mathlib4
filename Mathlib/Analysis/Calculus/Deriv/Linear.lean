/-
Copyright (c) 2019 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Yury Kudryashov
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Linear

#align_import analysis.calculus.deriv.linear from "leanprover-community/mathlib"@"3bce8d800a6f2b8f63fe1e588fd76a9ff4adcebe"

/-!
# Derivatives of continuous linear maps from the base field

In this file we prove that `f : 𝕜 →L[𝕜] E` (or `f : 𝕜 →ₗ[𝕜] E`) has derivative `f 1`.

For a more detailed overview of one-dimensional derivatives in mathlib, see the module docstring of
`Analysis/Calculus/Deriv/Basic`.

## Keywords

derivative, linear map
-/


universe u v w

open Topology Filter

open Filter Asymptotics Set

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {E : Type w} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {x : 𝕜}
variable {s : Set 𝕜}
variable {L : Filter 𝕜}

section ContinuousLinearMap

/-! ### Derivative of continuous linear maps -/

variable (e : 𝕜 →L[𝕜] F)

protected theorem ContinuousLinearMap.hasDerivAtFilter : HasDerivAtFilter e (e 1) x L :=
  e.hasFDerivAtFilter.hasDerivAtFilter
#align continuous_linear_map.has_deriv_at_filter ContinuousLinearMap.hasDerivAtFilter

protected theorem ContinuousLinearMap.hasStrictDerivAt : HasStrictDerivAt e (e 1) x :=
  e.hasStrictFDerivAt.hasStrictDerivAt
#align continuous_linear_map.has_strict_deriv_at ContinuousLinearMap.hasStrictDerivAt

protected theorem ContinuousLinearMap.hasDerivAt : HasDerivAt e (e 1) x :=
  e.hasDerivAtFilter
#align continuous_linear_map.has_deriv_at ContinuousLinearMap.hasDerivAt

protected theorem ContinuousLinearMap.hasDerivWithinAt : HasDerivWithinAt e (e 1) s x :=
  e.hasDerivAtFilter
#align continuous_linear_map.has_deriv_within_at ContinuousLinearMap.hasDerivWithinAt

@[simp]
protected theorem ContinuousLinearMap.deriv : deriv e x = e 1 :=
  e.hasDerivAt.deriv
#align continuous_linear_map.deriv ContinuousLinearMap.deriv

protected theorem ContinuousLinearMap.derivWithin (hxs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin e s x = e 1 :=
  e.hasDerivWithinAt.derivWithin hxs
#align continuous_linear_map.deriv_within ContinuousLinearMap.derivWithin

end ContinuousLinearMap

section LinearMap

/-! ### Derivative of bundled linear maps -/

variable (e : 𝕜 →ₗ[𝕜] F)

protected theorem LinearMap.hasDerivAtFilter : HasDerivAtFilter e (e 1) x L :=
  e.toContinuousLinearMap₁.hasDerivAtFilter
#align linear_map.has_deriv_at_filter LinearMap.hasDerivAtFilter

protected theorem LinearMap.hasStrictDerivAt : HasStrictDerivAt e (e 1) x :=
  e.toContinuousLinearMap₁.hasStrictDerivAt
#align linear_map.has_strict_deriv_at LinearMap.hasStrictDerivAt

protected theorem LinearMap.hasDerivAt : HasDerivAt e (e 1) x :=
  e.hasDerivAtFilter
#align linear_map.has_deriv_at LinearMap.hasDerivAt

protected theorem LinearMap.hasDerivWithinAt : HasDerivWithinAt e (e 1) s x :=
  e.hasDerivAtFilter
#align linear_map.has_deriv_within_at LinearMap.hasDerivWithinAt

@[simp]
protected theorem LinearMap.deriv : deriv e x = e 1 :=
  e.hasDerivAt.deriv
#align linear_map.deriv LinearMap.deriv

protected theorem LinearMap.derivWithin (hxs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin e s x = e 1 :=
  e.hasDerivWithinAt.derivWithin hxs
#align linear_map.deriv_within LinearMap.derivWithin

end LinearMap
