/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# Quadratic forms are line (Gateaux) differentiable

In this file we prove that a quadratic form is line differentiable,
with the line derivative given by the polar bilinear form.
Note that this statement does not need topology on the domain.
In particular, it applies to discontinuous quadratic forms on infinite dimensional spaces.
-/

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]

namespace QuadraticForm

theorem hasLineDerivAt (f : QuadraticForm 𝕜 E) (a b : E) :
    HasLineDerivAt 𝕜 f (polar f a b) a b := by
  simpa [HasLineDerivAt, QuadraticForm.map_add, f.map_smul, mul_assoc]
    using ((hasDerivAt_const (0 : 𝕜) (f a)).add
      ((hasDerivAt_id _).mul (hasDerivAt_mul_const _))).add (hasDerivAt_mul_const _)

theorem lineDifferentiableAt (f : QuadraticForm 𝕜 E) (a b : E) : LineDifferentiableAt 𝕜 f a b :=
  (f.hasLineDerivAt a b).lineDifferentiableAt

@[simp]
protected theorem lineDeriv (f : QuadraticForm 𝕜 E) : lineDeriv 𝕜 f = polar f := by
  ext a b
  exact (f.hasLineDerivAt a b).lineDeriv

end QuadraticForm
