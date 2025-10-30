/-
Copyright (c) 2025 George McNinch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George McNinch
-/

import Mathlib.Algebra.Polynomial.Module.Basic
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# PolynomialModule is isomorphic to a tensor product
For a commutative ring `R` and an `R`-module `M`, we obtain an isomorphism between
`R[X] ⊗[R] M` and `PolynomialModule R M` as `R[X]`-modules; this isomorphism is called
`polynomialTensorProductLEquivPolynomialModule`.
-/

open Polynomial TensorProduct LinearMap

noncomputable section

variable (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]

namespace PolynomialModule

/-- The `R[X]`-linear equivalence `(R[X] ⊗[R] M) ≃ₗ[R[X]] (PolynomialModule R M)`.
-/
def polynomialTensorProductLEquivPolynomialModule :
    R[X] ⊗[R] M ≃ₗ[R[X]] PolynomialModule R M :=
  let e := liftBaseChange R[X] <| lsingle R (M := M) 0
  let inv := (eval X).restrictScalars R ∘ₗ map R[X] (TensorProduct.mk R R[X] M 1)
  have left : inv ∘ₗ e = .id := by
    ext n x
    simp [inv, e, ← monomial_one_right_eq_X_pow, smul_tmul']
  have right : e.restrictScalars R ∘ₗ inv = .id := by
    ext n x
    simp [e, inv, ← monomial_one_right_eq_X_pow]
  { __ := e
    invFun := inv
    left_inv := (congr($left ·))
    right_inv := (congr($right ·)) }

end PolynomialModule
