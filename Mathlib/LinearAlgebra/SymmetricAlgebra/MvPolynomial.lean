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

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- `SymmetricAlgebra.isoMvPolynomial` give an algebra isomorphism between symmetric algebra over a
free module and multivariate polynomial over the basis. -/
noncomputable def SymmetricAlgebra.isoMvPolynomial {I : Type*} (h : Basis I R M) :
    SymmetricAlgebra R M ≃ₐ[R] MvPolynomial I R := .ofAlgHom
  (SymmetricAlgebra.lift <| Basis.constr h R .X) (MvPolynomial.aeval fun i ↦ ι R M (h i))
  (MvPolynomial.algHom_ext fun i ↦ by simp) (algHom_ext <| h.ext fun i ↦ by simp)

theorem IsSymmetricAlgebra.mvPolynomial (I : Type*) (h : Basis I R M) :
    IsSymmetricAlgebra (Basis.constr h R (.X : I → MvPolynomial I R)) :=
  (SymmetricAlgebra.isoMvPolynomial h).bijective
