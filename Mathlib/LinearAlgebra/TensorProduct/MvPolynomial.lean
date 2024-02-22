/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.Data.MvPolynomial.Basic
import Mathlib.RingTheory.TensorProduct
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
    MvPolynomial.rTensor' (p ⊗ₜ[R] n) =
      p.sum (fun i m ↦ Finsupp.single i (m ⊗ₜ[R] n)) :=
  TensorProduct.finsuppLeft_apply_tmul p n

lemma MvPolynomial.rTensor'_apply_tmul_apply (p : MvPolynomial σ S) (n : N) (d : σ →₀ ℕ) :
    MvPolynomial.rTensor' (p ⊗ₜ[R] n) d =
      (coeff d p) ⊗ₜ[R] n :=
  TensorProduct.finsuppLeft_apply_tmul_apply p n d

lemma MvPolynomial.rTensor'_symm_apply_single (d : σ →₀ ℕ) (s : S) (n : N) :
    MvPolynomial.rTensor'.symm (Finsupp.single d (s ⊗ₜ n)) =
      (MvPolynomial.monomial d s) ⊗ₜ[R] n :=
  TensorProduct.finsuppLeft_symm_apply_single d s n

noncomputable def MvPolynomial.rTensor :
    MvPolynomial σ R ⊗[R] N ≃ₗ[R] (σ →₀ ℕ) →₀ N :=
  TensorProduct.finsuppScalarLeft

lemma MvPolynomial.rTensor_apply_tmul (p : MvPolynomial σ R) (n : N) :
    MvPolynomial.rTensor (p ⊗ₜ[R] n) =
      p.sum (fun i m ↦ Finsupp.single i (m • n)) :=
  TensorProduct.finsuppScalarLeft_apply_tmul p n

lemma MvPolynomial.rTensor_apply_tmul_apply (p : MvPolynomial σ R) (n : N) (d : σ →₀ ℕ):
    MvPolynomial.rTensor (p ⊗ₜ[R] n) d = (coeff d p) • n :=
  TensorProduct.finsuppScalarLeft_apply_tmul_apply p n d

lemma MvPolynomial.rTensor_symm_apply_single (d : σ →₀ ℕ) (n : N) :
    MvPolynomial.rTensor.symm (Finsupp.single d n) =
      (MvPolynomial.monomial d 1) ⊗ₜ[R] n :=
  TensorProduct.finsuppScalarLeft_symm_apply_single d n
end

#exit
-- DOES NOT WORK YET

section MonoidAlgebra

open TensorProduct
variable (α : Type*) [Monoid α] [DecidableEq α]
  (R : Type*) [CommSemiring R]
  (N : Type*) [Semiring N] [Algebra R N]

noncomputable example : Semiring (MonoidAlgebra R α) := inferInstance

noncomputable example : Algebra R (MonoidAlgebra R α) := inferInstance

noncomputable example : Semiring ((MonoidAlgebra R α) ⊗[R] N) := inferInstance

noncomputable example : Algebra R ((MonoidAlgebra R α) ⊗[R] N) := inferInstance


variable {α R N}

noncomputable def MonoidAlgebra.AlgEquiv
  {N' : Type*} [Semiring N'] [Algebra R N'] (e : N ≃ₐ[R] N') :
    MonoidAlgebra N α ≃ₐ[R] MonoidAlgebra N' α := {
  Finsupp.mapRange.linearEquiv e.toLinearEquiv with
  map_mul' := fun x y => by
    simp
    ext
    sorry
  commutes' := sorry  }

noncomputable def MonoidAlgebra.rTensorEquiv :
    (MonoidAlgebra R α) ⊗[R] N ≃ₗ[R] MonoidAlgebra N α :=
  (TensorProduct.finsuppLeft (R := R) (ι := α) (M := R) (N := N)).trans
    (MonoidAlgebra.AlgEquiv (α := α) (Algebra.TensorProduct.lid R N)).toLinearEquiv

example (f g : (MonoidAlgebra R α) ⊗[R] N) :
    MonoidAlgebra.rTensorEquiv (N := N) (R := R) (f * g) =
      MonoidAlgebra.rTensorEquiv f * MonoidAlgebra.rTensorEquiv g := by
  induction f using TensorProduct.induction_on with
  | zero => simp only [zero_mul, LinearEquiv.map_zero]
  | tmul f n => sorry
  | add => sorry

noncomputable example : (MonoidAlgebra R α) ⊗[R] N ≃ₐ[R] MonoidAlgebra N α := {
  MonoidAlgebra.rTensorEquiv with
  map_mul' := fun f g ↦ by
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
      LinearEquiv.trans_apply]
    apply MonoidAlgebra.induction_on
    · intro a
      apply MonoidAlgebra.induction_on
      · intro b
        simp only [MonoidAlgebra.of_apply]
        sorry
      · sorry
      · sorry
    · sorry -- add
    · sorry -- hsmul
  commutes' := sorry }
