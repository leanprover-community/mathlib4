/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Analysis.NormedSpace.ContinuousAffineMap
import Mathlib.Analysis.Calculus.ContDiff.Basic

#align_import analysis.calculus.affine_map from "leanprover-community/mathlib"@"839b92fedff9981cf3fe1c1f623e04b0d127f57c"

/-!
# Smooth affine maps

This file contains results about smoothness of affine maps.

## Main definitions:

 * `ContinuousAffineMap.contDiff`: a continuous affine map is smooth

-/


namespace ContinuousAffineMap

variable {𝕜 V W : Type*} [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup V] [NormedSpace 𝕜 V]
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]

/-- A continuous affine map between normed vector spaces is smooth. -/
theorem contDiff {n : ℕ∞} (f : V →ᴬ[𝕜] W) : ContDiff 𝕜 n f := by
  rw [f.decomp]
  apply f.contLinear.contDiff.add
  exact contDiff_const
#align continuous_affine_map.cont_diff ContinuousAffineMap.contDiff

end ContinuousAffineMap
