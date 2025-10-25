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
  let e := liftBaseChange R[X] <| PolynomialModule.lsingle R (M := M) 0
  let inv : PolynomialModule R M →ₗ[R] R[X] ⊗[R] M :=
    Finsupp.lsum R fun n ↦ TensorProduct.mk R R[X] M (X ^ n)
  have left : inv ∘ₗ e = .id := by
    ext n x
    simpa [inv, e] using (Finsupp.sum_single_index (by simp)).trans <| by
      simp [monomial_one_right_eq_X_pow]
  have right : e.restrictScalars R ∘ₗ inv = .id := by
    refine Finsupp.lhom_ext' fun n ↦ LinearMap.ext fun x ↦ ?_
    simpa [e, inv, ← monomial_one_right_eq_X_pow] using by rfl
  { __ := e
    invFun := inv
    left_inv := (congr($left ·))
    right_inv := (congr($right ·)) }

end PolynomialModule
