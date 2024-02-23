/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.Data.MvPolynomial.Basic

/-!

# Tensor Product of polynomial rings

-/


universe u v w

noncomputable section

open DirectSum TensorProduct

open Set LinearMap Submodule

variable {R : Type u} {M : Type v} {N : Type w}
  [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

variable {σ : Type u} [DecidableEq σ]

variable {S : Type*} [CommSemiring S] [Algebra R S]

noncomputable def MvPolynomial.rTensor' :
    MvPolynomial σ S ⊗[R] N ≃ₗ[S] (σ →₀ ℕ) →₀ (S ⊗[R] N) :=
  TensorProduct.finsuppLeft'

lemma MvPolynomial.rTensor'_apply_tmul (p : MvPolynomial σ S) (n : N) :
    MvPolynomial.rTensor' (p ⊗ₜ[R] n) = p.sum (fun i m ↦ Finsupp.single i (m ⊗ₜ[R] n)) :=
  TensorProduct.finsuppLeft_apply_tmul p n

lemma MvPolynomial.rTensor'_apply_tmul_apply (p : MvPolynomial σ S) (n : N) (d : σ →₀ ℕ) :
    MvPolynomial.rTensor' (p ⊗ₜ[R] n) d = (coeff d p) ⊗ₜ[R] n :=
  TensorProduct.finsuppLeft_apply_tmul_apply p n d

lemma MvPolynomial.rTensor'_symm_apply_single (d : σ →₀ ℕ) (s : S) (n : N) :
    MvPolynomial.rTensor'.symm (Finsupp.single d (s ⊗ₜ n)) =
      (MvPolynomial.monomial d s) ⊗ₜ[R] n :=
  TensorProduct.finsuppLeft_symm_apply_single d s n

noncomputable def MvPolynomial.rTensor :
    MvPolynomial σ R ⊗[R] N ≃ₗ[R] (σ →₀ ℕ) →₀ N :=
  TensorProduct.finsuppScalarLeft

lemma MvPolynomial.rTensor_apply_tmul (p : MvPolynomial σ R) (n : N) :
    MvPolynomial.rTensor (p ⊗ₜ[R] n) = p.sum (fun i m ↦ Finsupp.single i (m • n)) :=
  TensorProduct.finsuppScalarLeft_apply_tmul p n

lemma MvPolynomial.rTensor_apply_tmul_apply (p : MvPolynomial σ R) (n : N) (d : σ →₀ ℕ):
    MvPolynomial.rTensor (p ⊗ₜ[R] n) d = (coeff d p) • n :=
  TensorProduct.finsuppScalarLeft_apply_tmul_apply p n d

lemma MvPolynomial.rTensor_symm_apply_single (d : σ →₀ ℕ) (n : N) :
    MvPolynomial.rTensor.symm (Finsupp.single d n) = (MvPolynomial.monomial d 1) ⊗ₜ[R] n :=
  TensorProduct.finsuppScalarLeft_symm_apply_single d n
end
