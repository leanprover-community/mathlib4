/-
Copyright (c) 2025 Raphael Douglas Giles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Douglas Giles, Zhixuan Dai, Zhenyan Fu, Yiming Fu, Jingting Wang
-/
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Main Definitions

1. `SymmetricAlgebra.isoMvPolynomial` give an algebra isomorphism between symmetric algebra over a
  free module and multivariate polynomial over the basis.
-/

variable {R L : Type*} [CommSemiring R] [AddCommMonoid L] [Module R L]

/-- `SymmetricAlgebra.isoMvPolynomial` give an algebra isomorphism between symmetric algebra over a
  free module and multivariate polynomial over the basis. -/
noncomputable def SymmetricAlgebra.isoMvPolynomial {I : Type*} (h : Basis I R L) :
    SymmetricAlgebra R L ≃ₐ[R] MvPolynomial I R := .ofAlgHom
  (SymmetricAlgebra.lift (Basis.constr h R (fun i ↦ ((MvPolynomial.X i) : (MvPolynomial I R)))))
  (MvPolynomial.aeval (R := R) (fun i ↦ SymmetricAlgebra.ι R L (h i)))
  (MvPolynomial.algHom_ext fun i ↦ (by simp))
  (SymmetricAlgebra.algHom_ext <| h.ext fun i ↦ by simp)

theorem IsSymmetricAlgebra.mvPolynomial (I : Type*) (h : Basis I R L) :
    IsSymmetricAlgebra (Basis.constr h R fun i ↦ (.X i : MvPolynomial I R)) := by
  exact (SymmetricAlgebra.isoMvPolynomial h).bijective
