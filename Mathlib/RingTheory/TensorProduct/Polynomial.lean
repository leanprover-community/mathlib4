/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Algebra.Polynomial.Eval

/-! # Tensor products of a polynomial ring

Adaptations of `TensorProduct.finsuppLeft` when the `Finsupp` is a `Polynomial`.

* `Polynomial.rTensor`, `Polynomial.scalarRTensor`, the linear map
  from the tensor product of a polynomial ring to a Finsupp type;
* `Polynomial.mapAlgHom`, `Polynomial.mapAlgEquiv`, the alg hom and the alg equiv
  between polynomial rings induced by an alg hom on coefficients
* `Polynomial.rTensorAlgHom`, the alg hom morphism from the tensor product of
    a polynomial ring to an algebra to a polynomial ring
* `Polynomial.rTensorLinearEquiv`, the corresponding linear equiv
* `Polynomial.rTensorAlgEquiv`, `Polynomial.scalarRTensorAlgEquiv`, the corresponding alg equiv

## Notes

This is not just `MvPolynomial.rTensor` because `Polynomial` is not a particular
case of `MvPolynomial`.
Moreover, compared to `MonoidAlgebra`, the type `Polynomial` conceals its
underlying `Finsupp` function as `Polynomial.toFinsupp`,
so some rewriting is necessary.

## TODO

* `Polynomial.lTensor`

-/

universe u v w

variable {R : Type u} {M : Type v} {N : Type w}
  [CommSemiring R] [AddCommMonoid M] [Module R M]

variable {S : Type*} [CommSemiring S] [Algebra R S]

section Module

open Polynomial TensorProduct LinearMap

variable [AddCommMonoid N] [Module R N]

variable [Module S M] [IsScalarTower R S M] [Module S N] [IsScalarTower R S N]
    {P : Type*} [AddCommMonoid P] [Module R P]
    {Q : Type*} [AddCommMonoid Q] [Module R Q]

namespace Polynomial

open LinearEquiv

variable (R N)
/-- The linear map from the tensor product of a polynomial ring to a Finsupp type -/
noncomputable def scalarRTensor : R[X] ⊗[R] N ≃ₗ[R] ℕ →₀ N :=
  ((toFinsuppLinearEquiv R).rTensor N).trans (finsuppScalarLeft _ _ _)

variable {R N}
lemma scalarRTensor_apply_tmul_apply (p : R[X]) (n : N) (i : ℕ) :
    scalarRTensor R N (p ⊗ₜ[R] n) i = coeff p i • n := by
  simp only [scalarRTensor, LinearEquiv.trans_apply]
  simp only [LinearEquiv.rTensor, congr_tmul, refl_apply]
  apply finsuppScalarLeft_apply_tmul_apply

lemma scalarRTensor_apply_tmul (p : R[X]) (n : N) :
    scalarRTensor R N (p ⊗ₜ[R] n) = p.sum (fun i r => Finsupp.single i (r • n)) := by
  ext i
  rw [scalarRTensor_apply_tmul_apply]
  rw [sum_def]
  rw [Finset.sum_apply']
  rw [Finset.sum_eq_single i]
  · simp only [Finsupp.single_eq_same]
  · exact fun _ _ => Finsupp.single_eq_of_ne
  · intro h
    simp only [mem_support_iff, ne_eq, not_not] at h
    rw [h, zero_smul, Finsupp.single_zero, Finsupp.coe_zero, Pi.zero_apply]

lemma scalarRTensor_apply (pn : R[X] ⊗[R] N) (d : ℕ) :
    scalarRTensor R N pn d = TensorProduct.lid R N ((lcoeff R d).rTensor N pn) := by
  rw [← LinearEquiv.symm_apply_eq, lid_symm_apply]
  induction pn using TensorProduct.induction_on with
  | zero => simp
  | tmul p n => simp [scalarRTensor_apply_tmul_apply, TensorProduct.smul_tmul']
  | add x y hx hy => simp [tmul_add, hx, hy]

variable (R S N)
/-- The linear map from the tensor product of a polynomial ring to a Finsupp type -/
noncomputable def rTensor : S[X] ⊗[R] N ≃ₗ[S] ℕ →₀ (S ⊗[R] N) :=
  (TensorProduct.AlgebraTensorModule.rTensor N (toFinsuppLinearEquiv S)).trans (TensorProduct.finsuppLeft' _ _ _ _ S)

variable {R S N}
lemma rTensor_apply_tmul_apply (p : Polynomial S) (n : N) (i : ℕ) :
    rTensor R N S (p ⊗ₜ[R] n) i = (coeff p i) ⊗ₜ[R] n := by
  simp only [rTensor, LinearEquiv.trans_apply, finsuppLeft'_apply]
  simp only [TensorProduct.AlgebraTensorModule.rTensor_apply, LinearEquiv.rTensor, congr_tmul,
    LinearEquiv.restrictScalars_apply, LinearEquiv.refl_apply]
  simp only [toFinsuppLinearEquiv, RingEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe,
    Equiv.invFun_as_coe, LinearEquiv.coe_mk, toFinsuppIso_apply]
  erw [finsuppLeft'_apply (R := R) (S := S)]
  apply finsuppLeft_apply_tmul_apply

lemma rTensor_apply_tmul (p : Polynomial S) (n : N) :
    rTensor R N S (p ⊗ₜ[R] n) = p.sum (fun i m ↦ Finsupp.single i (m ⊗ₜ[R] n)) := by
  simp only [rTensor, LinearEquiv.trans_apply, finsuppLeft'_apply,
    TensorProduct.AlgebraTensorModule.rTensor_apply, LinearEquiv.rTensor]
  simp only [congr_tmul, LinearEquiv.restrictScalars_apply, refl_apply]
  simp only [toFinsuppLinearEquiv, RingEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe,
    Equiv.invFun_as_coe, LinearEquiv.coe_mk, toFinsuppIso_apply]
  erw [finsuppLeft'_apply (R := R) (S := S)]
  apply finsuppLeft_apply_tmul

lemma rTensor_apply (t : Polynomial S ⊗[R] N) (d : ℕ) :
    rTensor R N S t d = ((lcoeff S d).restrictScalars R).rTensor N t := by
  simp only [rTensor, trans_apply, AlgebraTensorModule.rTensor_apply, LinearEquiv.rTensor]
  erw [finsuppLeft'_apply]
  simp only [TensorProduct.congr, refl_toLinearMap, refl_symm, ofLinear_apply, finsuppLeft_apply,
    LinearMap.rTensor]
  erw [← LinearMap.comp_apply, ← TensorProduct.map_comp]
  rfl

end Polynomial

end Module

section Algebra

open TensorProduct LinearMap
namespace Polynomial

variable [CommSemiring N] [Algebra R N]

section

variable {R A B : Type*} [CommSemiring R]
    [CommSemiring A] [Algebra R A]
    [CommSemiring B] [Algebra R B]

/-- The alg hom between polynomial rings induced by an alg hom on coefficients -/
noncomputable def mapAlgHom (f : A →ₐ[R] B) :
    A[X] →ₐ[R] B[X] := {
  mapRingHom (f : A →+* B) with
  commutes' := fun r => by
    have hA : (algebraMap R A[X]) r = C ((algebraMap R A) r) := rfl
    have hB : (algebraMap R B[X]) r = C ((algebraMap R B) r) := rfl
    rw [hA, hB]
    simp
  toFun := map (f : A →+* B) }

/-- If `e : A ≃ₐ[R] B` is an isomorphism of `R`-algebras, then so is `mapAlgHom e`. -/
@[simps apply]
noncomputable def mapAlgEquiv (e : A ≃ₐ[R] B) :
    Polynomial A ≃ₐ[R] Polynomial B :=
  { mapAlgHom (e : A →ₐ[R] B), mapEquiv (e : A ≃+* B) with
    toFun := map (e : A →+* B) }

end

variable (R N S)
/-- The alg hom morphism from the tensor product of a polynomial ring to
  an algebra to a polynomial ring -/
noncomputable def rTensorAlgHom :
    (Polynomial S) ⊗[R] N →ₐ[S] Polynomial (S ⊗[R] N) :=
  Algebra.TensorProduct.lift
    (mapAlgHom Algebra.TensorProduct.includeLeft)
    ((IsScalarTower.toAlgHom R (S ⊗[R] N) _).comp Algebra.TensorProduct.includeRight)
    (fun p n => by simp only [commute_iff_eq, mul_comm])

variable {R N S}

lemma rTensorAlgHom_coeff_apply_tmul
    (p : Polynomial S) (n : N) (d : ℕ) :
    coeff (rTensorAlgHom R N S (p ⊗ₜ[R] n)) d = (coeff p d) ⊗ₜ[R] n := by
  rw [rTensorAlgHom, Algebra.TensorProduct.lift_tmul]
  rw [AlgHom.coe_comp, IsScalarTower.coe_toAlgHom', Function.comp_apply,
    Algebra.TensorProduct.includeRight_apply]
  rw [← C_eq_algebraMap, mul_comm, coeff_C_mul]
  simp [mapAlgHom, coeff_map]

variable (R S N)
/-- The linear equiv from the tensor product of a polynomial ring by an algebra
  to a polynomial ring -/
noncomputable def rTensorLinearEquiv : S[X] ⊗[R] N ≃ₗ[S] (S ⊗[R] N)[X] :=
  (TensorProduct.AlgebraTensorModule.rTensor N (toFinsuppLinearEquiv S)).trans
    ((finsuppLeft' _ _ _ _ S).trans
      ((toFinsuppLinearEquiv _).symm.restrictScalars _))

variable {R N S}

lemma rTensorLinearEquiv_coe (p : Polynomial S) (n : N) :
    (rTensorLinearEquiv R N S (p ⊗ₜ[R] n)).toFinsupp = TensorProduct.finsuppLeft' _ _ _ _ S (p.toFinsupp ⊗ₜ[R] n) := rfl

lemma rTensorLinearEquiv_coeff_tmul (p : Polynomial S) (n : N) (e : ℕ) :
    coeff (rTensorLinearEquiv R N S (p ⊗ₜ[R] n)) e = (coeff p e) ⊗ₜ[R] n := by
  simp only [coeff, AddHom.toFun_eq_coe, coe_toAddHom, LinearEquiv.coe_coe]
  rw [rTensorLinearEquiv_coe, finsuppLeft'_apply, finsuppLeft_apply_tmul_apply]

lemma rTensorAlgHom_toLinearMap :
    (rTensorAlgHom R N S).toLinearMap
      = (rTensorLinearEquiv _ _ _).toLinearMap:= by
  ext d n e
  dsimp only [AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
    LinearMap.coe_restrictScalars, AlgHom.toLinearMap_apply]
  simp only [coe_comp, Function.comp_apply, AlgebraTensorModule.curry_apply, curry_apply,
    LinearMap.coe_restrictScalars, AlgHom.toLinearMap_apply, LinearEquiv.coe_coe]
  rw [rTensorAlgHom_coeff_apply_tmul, rTensorLinearEquiv_coeff_tmul]

lemma rTensorAlgHom_apply_eq (p : Polynomial S ⊗[R] N) :
    rTensorAlgHom R N S p = rTensorLinearEquiv R N S p := by
  rw [← AlgHom.toLinearMap_apply, rTensorAlgHom_toLinearMap]
  rfl

variable (R N S)

/-- The alg equiv from the tensor product of a polynomial ring and an algebra
  to a polynomial ring -/
noncomputable def rTensorAlgEquiv :
    (Polynomial S) ⊗[R] N ≃ₐ[S] Polynomial (S ⊗[R] N) := by
  apply AlgEquiv.ofLinearEquiv (rTensorLinearEquiv R N S)
  · simp only [Algebra.TensorProduct.one_def]
    apply symm
    ext e
    simp only [rTensorLinearEquiv_coeff_tmul, coeff_one]
    split_ifs; rfl; simp only [zero_tmul]
  · intro x y
    erw [← rTensorAlgHom_apply_eq (S := S)]
    simp only [_root_.map_mul, rTensorAlgHom_apply_eq]

/-- The tensor product of a polynomial ring  with an algebra is a polynomial ring -/
noncomputable def scalarRTensorAlgEquiv :
    R[X] ⊗[R] N ≃ₐ[R] Polynomial N :=
  (rTensorAlgEquiv R N R).trans (mapAlgEquiv (Algebra.TensorProduct.lid R N))

end Polynomial

end Algebra
