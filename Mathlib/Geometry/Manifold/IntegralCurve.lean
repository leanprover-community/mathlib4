/-
Copyright (c) 2023 Winston Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin
-/
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Geometry.Manifold.ContMDiff
import Mathlib.Geometry.Manifold.MFDeriv

/-!
# Integral curves of vector fields on a manifold

For any continuously differentiable vector field on a manifold `M` and any chosen non-boundary point
`x₀ : M`, an integral curve `γ : ℝ → M` exists such that `γ t₀ = x₀` and the tangent vector of `γ`
at `t` coincides with the vector field at `γ t` for all `t` within an open interval around `t₀`.

As a corollary, such an integral curve exists for any starting point `x₀` if `M` is a manifold
without boundary.

## Implementation details

Since there is already an ODE solution existence theorem
`IsPicardLindelof.exists_forall_hasDerivWithinAt_Icc_eq`, the bulk of this file is to convert
statements about manifolds to statements about the model space. This comes in a few steps:
1. Express the smoothness of the vector field `v` in a single fixed chart around the starting point
`x₀`.
2. Use the ODE solution existence theorem to obtain a curve `γ : ℝ → M` whose derivative coincides
with the vector field (stated in the local chart around `x₀`).
3. Same as 2 but now stated in the local chart around `γ t`, which is how `cont_mdiff` is defined.

## Tags

integral curve, vector field
-/
