/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Linear
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
/-!
# Derivatives of affine maps

In this file we prove formulas for one-dimensional derivatives of affine maps `f : 𝕜 →ᵃ[𝕜] E`. We
also specialise some of these results to `AffineMap.lineMap` because it is useful to transfer MVT
from dimension 1 to a domain in higher dimension.

## TODO

Add theorems about `deriv`s and `fderiv`s of `ContinuousAffineMap`s once they will be ported to
Mathlib 4.

## Keywords

affine map, derivative, differentiability
-/

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  (f : 𝕜 →ᵃ[𝕜] E) {a b : E} {L : Filter 𝕜} {s : Set 𝕜} {x : 𝕜}

namespace AffineMap

theorem hasStrictDerivAt : HasStrictDerivAt f (f.linear 1) x := by
  rw [f.decomp]
  exact f.linear.hasStrictDerivAt.add_const (f 0)

theorem hasDerivAtFilter : HasDerivAtFilter f (f.linear 1) x L := by
  rw [f.decomp]
  exact f.linear.hasDerivAtFilter.add_const (f 0)

theorem hasDerivWithinAt : HasDerivWithinAt f (f.linear 1) s x := f.hasDerivAtFilter
theorem hasDerivAt : HasDerivAt f (f.linear 1) x := f.hasDerivAtFilter

protected theorem derivWithin (hs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin f s x = f.linear 1 :=
  f.hasDerivWithinAt.derivWithin hs

@[simp] protected theorem deriv : deriv f x = f.linear 1 := f.hasDerivAt.deriv

protected theorem differentiableAt : DifferentiableAt 𝕜 f x := f.hasDerivAt.differentiableAt
protected theorem differentiable : Differentiable 𝕜 f := fun _ ↦ f.differentiableAt

protected theorem differentiableWithinAt : DifferentiableWithinAt 𝕜 f s x :=
  f.differentiableAt.differentiableWithinAt

protected theorem differentiableOn : DifferentiableOn 𝕜 f s := fun _ _ ↦ f.differentiableWithinAt

/-!
### Line map

In this section we specialize some lemmas to `AffineMap.lineMap` because this map is very useful to
deduce higher-dimensional lemmas from one-dimensional versions.
-/

theorem hasStrictDerivAt_lineMap : HasStrictDerivAt (lineMap a b) (b - a) x := by
  simpa using (lineMap a b : 𝕜 →ᵃ[𝕜] E).hasStrictDerivAt

theorem hasDerivAt_lineMap :  HasDerivAt (lineMap a b) (b - a) x :=
  hasStrictDerivAt_lineMap.hasDerivAt

theorem hasDerivWithinAt_lineMap : HasDerivWithinAt (lineMap a b) (b - a) s x :=
  hasDerivAt_lineMap.hasDerivWithinAt

end AffineMap
