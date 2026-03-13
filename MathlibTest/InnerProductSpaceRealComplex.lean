/-
Copyright (c) 2024 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Test: `instInnerProductSpaceRealComplex` is canonical at `instances` transparency

Previously `instInnerProductSpaceRealComplex` was defined as `InnerProductSpace.complexToReal`,
which goes through `NormedSpace.restrictScalars ℝ ℂ ℂ`. The `Module ℝ ℂ` arising from that path
disagrees with `Algebra.toModule ℝ ℂ` at `.instances` transparency, causing `rw [one_smul]` to
fail with `set_option backward.isDefEq.respectTransparency true`.

The fix redefines `instInnerProductSpaceRealComplex := RCLike.toInnerProductSpaceReal`, whose
`NormedSpace ℝ ℂ` comes from `NormedAlgebra.toNormedSpace` (via `RCLike.toNormedAlgebra`),
so its `Module ℝ ℂ` agrees with `Algebra.toModule` at `.instances` transparency.
-/

-- The `Module ℝ ℂ` from `InnerProductSpace ℝ ℂ` now agrees with `Algebra.toModule` at instances
-- transparency.
example : (inferInstance : InnerProductSpace ℝ ℂ).toNormedSpace.toModule =
    (inferInstance : Algebra ℝ ℂ).toModule := by
  with_reducible_and_instances rfl

-- As a consequence, `rw [one_smul]` works with strict transparency.
set_option backward.isDefEq.respectTransparency true in
example (z : ℂ) : (1 : ℝ) • z = z := by
  rw [one_smul]
