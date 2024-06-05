/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Algebra.MvPolynomial.Equiv
/-!

# Tensor Product of (multivariate) polynomial rings

Let `Semiring R`, `Algebra R S` and `Module R N`.

* `MvPolynomial.rTensor` gives the linear equivalence
  `MvPolynomial σ S ⊗[R] N ≃ₗ[R] (σ →₀ ℕ) →₀ (S ⊗[R] N)` characterized,
  for `p : MvPolynomial σ S`, `n : N` and `d : σ →₀ ℕ`, by
  `rTensor (p ⊗ₜ[R] n) d = (coeff d p) ⊗ₜ[R] n`
* `MvPolynomial.scalarRTensor` gives the linear equivalence
  `MvPolynomial σ R ⊗[R] N ≃ₗ[R] (σ →₀ ℕ) →₀ N`
  such that `MvPolynomial.scalarRTensor (p ⊗ₜ[R] n) d = coeff d p • n`
  for `p : MvPolynomial σ R`, `n : N` and `d : σ →₀ ℕ`, by

* `MvPolynomial.rTensorAlgHom`, the algebra morphism from the tensor product
  of a polynomial algebra by an algebra to a polynomial algebra
* `MvPolynomial.rTensorAlgEquiv`, `MvPolynomial.scalarRTensorAlgEquiv`,
  the tensor product of a polynomial algebra by an algebra
  is algebraically equivalent to a polynomial algebra

## TODO :
* `MvPolynomial.rTensor` could be phrased in terms of `AddMonoidAlgebra`, and
  `MvPolynomial.rTensor` then has `smul` by the polynomial algebra.
* `MvPolynomial.rTensorAlgHom` and `MvPolynomial.scalarRTensorAlgEquiv`
  are morphisms for the algebra structure by `MvPolynomial σ R`.
-/


universe u v w

noncomputable section

namespace MvPolynomial

open DirectSum TensorProduct

open Set LinearMap Submodule

variable {R : Type u} {M : Type v} {N : Type w}
  [CommSemiring R] [AddCommMonoid M] [Module R M]

variable {σ : Type*} [DecidableEq σ]

variable {S : Type*} [CommSemiring S] [Algebra R S]

section Module

variable [AddCommMonoid N] [Module R N]

/-- The tensor product of a polynomial ring by a module is
  linearly equivalent to a Finsupp of a tensor product -/
noncomputable def rTensor :
    MvPolynomial σ S ⊗[R] N ≃ₗ[S] (σ →₀ ℕ) →₀ (S ⊗[R] N) :=
  TensorProduct.finsuppLeft' _ _ _ _ _

lemma rTensor_apply_tmul (p : MvPolynomial σ S) (n : N) :
    rTensor (p ⊗ₜ[R] n) = p.sum (fun i m ↦ Finsupp.single i (m ⊗ₜ[R] n)) :=
  TensorProduct.finsuppLeft_apply_tmul p n

lemma rTensor_apply_tmul_apply (p : MvPolynomial σ S) (n : N) (d : σ →₀ ℕ) :
    rTensor (p ⊗ₜ[R] n) d = (coeff d p) ⊗ₜ[R] n :=
  TensorProduct.finsuppLeft_apply_tmul_apply p n d

lemma rTensor_apply_monomial_tmul (e : σ →₀ ℕ) (s : S) (n : N) (d : σ →₀ ℕ) :
    rTensor (monomial e s ⊗ₜ[R] n) d = if e = d then s ⊗ₜ[R] n else 0 := by
  simp only [rTensor_apply_tmul_apply, coeff_monomial, ite_tmul]

lemma rTensor_apply_X_tmul (s : σ) (n : N) (d : σ →₀ ℕ) :
    rTensor (X s ⊗ₜ[R] n) d = if Finsupp.single s 1 = d then (1 : S) ⊗ₜ[R] n else 0 := by
  rw [rTensor_apply_tmul_apply, coeff_X', ite_tmul]

lemma rTensor_apply (t : MvPolynomial σ S ⊗[R] N) (d : σ →₀ ℕ) :
    rTensor t d = ((lcoeff S d).restrictScalars R).rTensor N t :=
  TensorProduct.finsuppLeft_apply t d

@[simp]
lemma rTensor_symm_apply_single (d : σ →₀ ℕ) (s : S) (n : N) :
    rTensor.symm (Finsupp.single d (s ⊗ₜ n)) =
      (monomial d s) ⊗ₜ[R] n :=
  TensorProduct.finsuppLeft_symm_apply_single (R := R) d s n

/-- The tensor product of the polynomial algebra by a module
  is linearly equivalent to a Finsupp of that module -/
noncomputable def scalarRTensor :
    MvPolynomial σ R ⊗[R] N ≃ₗ[R] (σ →₀ ℕ) →₀ N :=
  TensorProduct.finsuppScalarLeft _ _ _

lemma scalarRTensor_apply_tmul (p : MvPolynomial σ R) (n : N) :
    scalarRTensor (p ⊗ₜ[R] n) = p.sum (fun i m ↦ Finsupp.single i (m • n)) :=
  TensorProduct.finsuppScalarLeft_apply_tmul p n

lemma scalarRTensor_apply_tmul_apply (p : MvPolynomial σ R) (n : N) (d : σ →₀ ℕ):
    scalarRTensor (p ⊗ₜ[R] n) d = coeff d p • n :=
  TensorProduct.finsuppScalarLeft_apply_tmul_apply p n d

lemma scalarRTensor_apply_monomial_tmul (e : σ →₀ ℕ) (r : R) (n : N) (d : σ →₀ ℕ):
    scalarRTensor (monomial e r ⊗ₜ[R] n) d = if e = d then r • n else 0 := by
  rw [scalarRTensor_apply_tmul_apply, coeff_monomial, ite_smul, zero_smul]

 lemma scalarRTensor_apply_X_tmul_apply (s : σ) (n : N) (d : σ →₀ ℕ):
    scalarRTensor (X s ⊗ₜ[R] n) d = if Finsupp.single s 1 = d then n else 0 := by
  rw [scalarRTensor_apply_tmul_apply, coeff_X', ite_smul, one_smul, zero_smul]

lemma scalarRTensor_symm_apply_single (d : σ →₀ ℕ) (n : N) :
    scalarRTensor.symm (Finsupp.single d n) = (monomial d 1) ⊗ₜ[R] n :=
  TensorProduct.finsuppScalarLeft_symm_apply_single d n

end Module

section Algebra

variable [CommSemiring N] [Algebra R N]

/-- The algebra morphism from a tensor product of a polynomial algebra
  by an algebra to a polynomial algebra -/
noncomputable def rTensorAlgHom :
    (MvPolynomial σ S) ⊗[R] N →ₐ[S] MvPolynomial σ (S ⊗[R] N) :=
  Algebra.TensorProduct.lift
    (mapAlgHom Algebra.TensorProduct.includeLeft)
    ((IsScalarTower.toAlgHom R (S ⊗[R] N) _).comp Algebra.TensorProduct.includeRight)
    (fun p n => by simp [commute_iff_eq, algebraMap_eq, mul_comm])

@[simp]
lemma coeff_rTensorAlgHom_tmul
    (p : MvPolynomial σ S) (n : N) (d : σ →₀ ℕ) :
    coeff d (rTensorAlgHom (p ⊗ₜ[R] n)) = (coeff d p) ⊗ₜ[R] n := by
  rw [rTensorAlgHom, Algebra.TensorProduct.lift_tmul]
  rw [AlgHom.coe_comp, IsScalarTower.coe_toAlgHom', Function.comp_apply,
    Algebra.TensorProduct.includeRight_apply]
  rw [algebraMap_eq, mul_comm, coeff_C_mul]
  simp [mapAlgHom, coeff_map]

lemma coeff_rTensorAlgHom_monomial_tmul
    (e : σ →₀ ℕ) (s : S) (n : N) (d : σ →₀ ℕ) :
    coeff d (rTensorAlgHom (monomial e s ⊗ₜ[R] n)) =
      if e = d then s ⊗ₜ[R] n else 0 := by
  simp [ite_tmul]

lemma rTensorAlgHom_toLinearMap :
    (rTensorAlgHom :
      MvPolynomial σ S ⊗[R] N →ₐ[S] MvPolynomial σ (S ⊗[R] N)).toLinearMap =
      rTensor.toLinearMap := by
  ext d n e
  dsimp only [AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
    LinearMap.coe_restrictScalars, AlgHom.toLinearMap_apply]
  simp only [coe_comp, Function.comp_apply, AlgebraTensorModule.curry_apply, curry_apply,
    LinearMap.coe_restrictScalars, AlgHom.toLinearMap_apply]
  rw [coeff_rTensorAlgHom_tmul]
  simp only [coeff]
  erw [finsuppLeft_apply_tmul_apply]

lemma rTensorAlgHom_apply_eq (p : MvPolynomial σ S ⊗[R] N) :
    rTensorAlgHom (S := S) p = rTensor p := by
  rw [← AlgHom.toLinearMap_apply, rTensorAlgHom_toLinearMap]
  rfl

/-- The tensor product of a polynomial algebra by an algebra
  is algebraically equivalent to a polynomial algebra -/
noncomputable def rTensorAlgEquiv :
    (MvPolynomial σ S) ⊗[R] N ≃ₐ[S] MvPolynomial σ (S ⊗[R] N) := by
  apply AlgEquiv.ofLinearEquiv rTensor
  · simp only [Algebra.TensorProduct.one_def]
    apply symm
    rw [← LinearEquiv.symm_apply_eq]
    exact finsuppLeft_symm_apply_single (R := R) (0 : σ →₀ ℕ) (1 : S) (1 : N)
  · intro x y
    erw [← rTensorAlgHom_apply_eq (S := S)]
    simp only [_root_.map_mul, rTensorAlgHom_apply_eq]
    rfl

/-- The tensor product of the polynomial algebra by an algebra
  is algebraically equivalent to a polynomial algebra with
  coefficients in that algegra -/
noncomputable def scalarRTensorAlgEquiv :
    MvPolynomial σ R ⊗[R] N ≃ₐ[R] MvPolynomial σ N :=
  rTensorAlgEquiv.trans (mapAlgEquiv σ (Algebra.TensorProduct.lid R N))

end Algebra

end MvPolynomial

end
