/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import Mathlib.Data.Polynomial.AlgebraMap
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Data.Polynomial.Eval
-- import Mathlib.LinearAlgebra.TensorProduct.Basic

/-! # Tensor products of a polynomial ring

Adaptations of `TensorProduct.finsuppLeft` when the `Finsupp` is a `Polynomial`.

* `LinearEquiv.rTensor`, `LinearEquiv.lTensor` : tensor a linear equivalence
  to the right or to the left gives a linear equivalence;
* `LinearEquiv.rTensor'`, `LinearEquiv.lTensor'` : tensor a linear equivalence
  to the right or to the left gives a linear equivalence, with more `smul` properties;
* `Polynomial.toFinsuppLinearEquiv`, the equivalen of the polynomial ring
  with a Finsupp type, as a linear equivalence;
* `Polynomial.rTensor`, `Polynomial.rTensor'`, the linear map
  from the tensor product of a polynomial ring to a Finsupp type;
* `Polynomial.mapAlgHom`, `Polynomial.mapAlgEquiv`, the alg hom and the alg equiv
  between polynomial rings induced by an alg hom on coefficients
* `Polynomial.rTensorAlgHom`, the alg hom morphism from the tensor product of
    a polynomial ring to an algebra to a polynomial ring
* `Polynomial.rTensorLinearEquiv`, the corresponding linear equiv
* `Polynomial.rTensorAlgEquiv`, `Polynomial.scalarRTensorAlgEquiv`, the corresponding alg equiv

## Notes

It is messy because `Polynomial` is not a `Finsupp`…
I believe most of this file should go elsewhere,
and maybe the small stuff that remains could be deleted.

## TODO

This will be obsolete when `MonoidAlgebra` will be aligned with `Polynomial`

-/
open TensorProduct LinearMap

universe u v w

variable {R : Type u} {M : Type v} {N : Type w}
  [CommSemiring R] [AddCommMonoid M] [Module R M]

variable {S : Type*} [CommSemiring S] [Algebra R S]

section Module

open Polynomial TensorProduct LinearMap

variable [AddCommMonoid N] [Module R N]

/-- Tensor a linear equivalence to the right gives a linear equivalence -/
noncomputable def LinearEquiv.rTensor
    (P : Type*) [AddCommMonoid P] [Module R P] (e : M ≃ₗ[R] N) :
    M ⊗[R] P ≃ₗ[R] N ⊗[R] P := congr e (refl R P)

/-- Tensor a linear equivalence to the left gives a linear equivalence -/
noncomputable def LinearEquiv.lTensor
    (P : Type*) (e : M ≃ₗ[R] N)  [AddCommMonoid P] [Module R P] :
    P ⊗[R] M ≃ₗ[R] P ⊗[R] N := congr (refl R P) e

variable [Module S M] [IsScalarTower R S M] [Module S N] [IsScalarTower R S N]
    {P : Type*} [AddCommMonoid P] [Module R P]
    {Q : Type*} [AddCommMonoid Q] [Module R Q]

/--  If `e` is `S`-linear, then `TensorProduct.map e f` is `S`-linear -/
noncomputable def TensorProduct.map' (e : M →ₗ[S] N) (f : P →ₗ[R] Q) :
    M ⊗[R] P →ₗ[S] N ⊗[R] Q where
  toFun := map (e.restrictScalars R) f
  map_add' := map_add _
  map_smul' := fun s t ↦ by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy =>
      simp only [smul_add, map_add] at hx hy ⊢
      simp only [hx, hy]
    | tmul m p =>
      rw [smul_tmul']
      simp only [map_tmul, coe_restrictScalars, map_smul]
      rfl

theorem TensorProduct.map'_restrictScalars (e : M →ₗ[S] N) (f : P →ₗ[R] Q) :
    (map' e f).restrictScalars R = map (e.restrictScalars R) f := rfl

theorem TensorProduct.map'_coe (e : M →ₗ[S] N) (f : P →ₗ[R] Q) :
    ⇑(map' e f) = ⇑(map (e.restrictScalars R) f) := rfl

/--  If `e` is a `S`-linear equivalence and `f` is an `R`-linear equivalence,
  then `TensorProduct.congr' e f` is a `S`-linear equivalence -/
noncomputable def TensorProduct.congr'
    (e : M ≃ₗ[S] N) (f : P ≃ₗ[R] Q) : M ⊗[R] P ≃ₗ[S] N ⊗[R] Q :=
  LinearEquiv.ofLinear (map' e f) (map' e.symm.toLinearMap f.symm)
    (by ext n q; simp [Function.comp_apply, map'_coe])
    (by ext m p; simp [Function.comp_apply, map'_coe])

theorem TensorProduct.congr'_restrictScalars (e : M ≃ₗ[S] N) (f : P ≃ₗ[R] Q) :
    (congr' e f).restrictScalars R = (congr (e.restrictScalars R) f) := rfl

theorem TensorProduct.congr'_coe (e : M ≃ₗ[S] N) (f : P ≃ₗ[R] Q) :
    ⇑(congr' e f) = ⇑(congr (e.restrictScalars R) f) := by
  rfl

/-
lemma TensorProduct.map_isLinearMap'
    [Module S M] [IsScalarTower R S M] [Module S N] [IsScalarTower R S N]
    {P : Type*} [AddCommMonoid P] [Module R P]
    {Q : Type*} [AddCommMonoid Q] [Module R Q]
    (e : M →ₗ[S] N) (f : P →ₗ[R] Q) :
    IsLinearMap S (TensorProduct.map (e.restrictScalars R) f) where
  map_add := LinearMap.map_add _
  map_smul := fun s t ↦ by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy =>
      simp only [smul_add, map_add] at hx hy ⊢
      simp only [hx, hy]
    | tmul m p =>
      rw [smul_tmul']
      simp only [map_tmul, coe_restrictScalars, map_smul]
      rfl
-/

/- lemma TensorProduct.congr_isLinearMap'
    [Module S M] [IsScalarTower R S M] [Module S N] [IsScalarTower R S N]
    {P : Type*} [AddCommMonoid P] [Module R P]
    {Q : Type*} [AddCommMonoid Q] [Module R Q]
    (e : M ≃ₗ[S] N) (f : P ≃ₗ[R] Q) :
    IsLinearMap S (TensorProduct.congr (e.restrictScalars R) f) :=
  TensorProduct.map_isLinearMap' e.toLinearMap f.toLinearMap -/

/-
lemma LinearEquiv.rTensor_isLinearMap'
    [Module S M] [IsScalarTower R S M] [Module S N] [IsScalarTower R S N]
    (P : Type*) [AddCommMonoid P] [Module R P] (e : M ≃ₗ[S] N) :
    IsLinearMap S (LinearEquiv.rTensor P (e.restrictScalars R)) :=
  TensorProduct.map_isLinearMap' e.toLinearMap _
-/

variable (P)
/-- Tensor a linear equivalence to the right or to the left gives a linear equivalence-/
noncomputable def LinearEquiv.rTensor' (e : M ≃ₗ[S] N) :
    M ⊗[R] P ≃ₗ[S] N ⊗[R] P := congr' e (LinearEquiv.refl R P)

lemma LinearEquiv.rTensor'_restrictScalars (e : M ≃ₗ[S] N) :
    (rTensor' P e).restrictScalars R = rTensor P (e.restrictScalars R) := rfl

lemma LinearEquiv.rTensor'_apply (e : M ≃ₗ[S] N) (mp : M ⊗[R] P) :
    rTensor' P e mp = rTensor P (e.restrictScalars R) mp := rfl

lemma LinearEquiv.rTensor'_coe (e : M ≃ₗ[S] N) :
    ⇑(rTensor' P e) = rTensor P (e.restrictScalars R) := rfl

namespace Polynomial

open LinearEquiv
variable (S)
/-- The equivalen of the polynomial ring with a Finsupp type, as a linear equivalence -/
def toFinsuppLinearEquiv : S[X] ≃ₗ[S] (ℕ →₀ S) := {
  toFinsuppIso S  with
  map_smul' := fun r p => by simp }

variable {S}
theorem toFinsuppLinearEquiv_apply (p : S[X]) :
    toFinsuppLinearEquiv S p = toFinsuppIso S p := rfl

/-- The linear map from the tensor product of a polynomial ring to a Finsupp type -/
noncomputable def scalarRTensor : R[X] ⊗[R] N ≃ₗ[R] ℕ →₀ N :=
  (LinearEquiv.rTensor N (toFinsuppLinearEquiv R)).trans finsuppScalarLeft

lemma scalarRTensor_apply_tmul_apply (p : R[X]) (n : N) (i : ℕ) :
    scalarRTensor (p ⊗ₜ[R] n) i = (coeff p i) • n := by
  simp only [scalarRTensor, LinearEquiv.trans_apply]
  simp only [LinearEquiv.rTensor, congr_tmul, refl_apply]
  rw [finsuppScalarLeft_apply_tmul_apply _ n i]
  rfl

lemma scalarRTensor_apply_tmul (p : R[X]) (n : N) :
    scalarRTensor (p ⊗ₜ[R] n) = p.sum (fun i r => Finsupp.single i (r • n)) := by
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
    scalarRTensor pn d = TensorProduct.lid R N ((Polynomial.lcoeff R d).rTensor N pn) := by
  rw [← LinearEquiv.symm_apply_eq, lid_symm_apply]
  induction pn using TensorProduct.induction_on with
  | zero => simp
  | tmul p n => simp [scalarRTensor_apply_tmul_apply, TensorProduct.smul_tmul']
  | add x y hx hy => simp [tmul_add, hx, hy]

/-- The linear map from the tensor product of a polynomial ring to a Finsupp type -/
noncomputable def rTensor : S[X] ⊗[R] N ≃ₗ[S] ℕ →₀ (S ⊗[R] N) :=
  (LinearEquiv.rTensor' N (toFinsuppLinearEquiv S)).trans TensorProduct.finsuppLeft'

lemma rTensor_apply_tmul_apply (p : Polynomial S) (n : N) (i : ℕ) :
    rTensor (p ⊗ₜ[R] n) i = (coeff p i) ⊗ₜ[R] n := by
  simp only [rTensor, LinearEquiv.trans_apply, finsuppLeft'_apply]
  simp only [LinearEquiv.rTensor'_apply, LinearEquiv.rTensor, congr_tmul,
    LinearEquiv.restrictScalars_apply, LinearEquiv.refl_apply]
  simp only [toFinsuppLinearEquiv, RingEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe,
    Equiv.invFun_as_coe, LinearEquiv.coe_mk, toFinsuppIso_apply]
  rw [finsuppLeft_apply_tmul_apply]
  rfl

end Polynomial

end Module

section Algebra

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

/-- The alg hom morphism from the tensor product of a polynomial ring to
  an algebra to a polynomial ring -/
noncomputable def rTensorAlgHom :
    (Polynomial S) ⊗[R] N →ₐ[S] Polynomial (S ⊗[R] N) :=
  Algebra.TensorProduct.lift
    (mapAlgHom Algebra.TensorProduct.includeLeft)
    ((IsScalarTower.toAlgHom R (S ⊗[R] N) _).comp Algebra.TensorProduct.includeRight)
    (fun p n => by simp only [commute_iff_eq, mul_comm])

lemma rTensorAlgHom_coeff_apply_tmul
    (p : Polynomial S) (n : N) (d : ℕ) :
    coeff (rTensorAlgHom (p ⊗ₜ[R] n)) d = (coeff p d) ⊗ₜ[R] n := by
  rw [rTensorAlgHom, Algebra.TensorProduct.lift_tmul]
  rw [AlgHom.coe_comp, IsScalarTower.coe_toAlgHom', Function.comp_apply,
    Algebra.TensorProduct.includeRight_apply]
  rw [← C_eq_algebraMap, mul_comm, coeff_C_mul]
  simp [mapAlgHom, coeff_map]

/-- The linear equiv from the tensor product of a polynomial ring by an algebra
  to a polynomial ring -/
noncomputable def rTensorLinearEquiv : S[X] ⊗[R] N ≃ₗ[S] (S ⊗[R] N)[X] :=
  ((LinearEquiv.rTensor' N (toFinsuppLinearEquiv S)).trans finsuppLeft').trans
    ((toFinsuppLinearEquiv _).symm.restrictScalars _)

lemma rTensorLinearEquiv_coeff_tmul (p : Polynomial S) (n : N) (e : ℕ) :
    coeff (rTensorLinearEquiv (S := S) (p ⊗ₜ[R] n)) e = (coeff p e) ⊗ₜ[R] n := by
  dsimp [coeff]
  have h : (rTensorLinearEquiv (S := S) (p ⊗ₜ[R] n)).toFinsupp
    = TensorProduct.finsuppLeft' (S := S) (p.toFinsupp ⊗ₜ[R] n) := by
    rfl
  rw [h, finsuppLeft'_apply, finsuppLeft_apply_tmul_apply]

lemma rTensorAlgHom_toLinearMap :
    (rTensorAlgHom.toLinearMap : (Polynomial S) ⊗[R] N →ₗ[S] Polynomial (S ⊗[R] N))
      = rTensorLinearEquiv.toLinearMap:= by
  ext d n e
  dsimp only [AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
    LinearMap.coe_restrictScalars, AlgHom.toLinearMap_apply]
  simp only [coe_comp, Function.comp_apply, AlgebraTensorModule.curry_apply, curry_apply,
    LinearMap.coe_restrictScalars, AlgHom.toLinearMap_apply, LinearEquiv.coe_coe]
  rw [rTensorAlgHom_coeff_apply_tmul, rTensorLinearEquiv_coeff_tmul]

lemma rTensorAlgHom_apply_eq (p : Polynomial S ⊗[R] N) :
    rTensorAlgHom (S := S) p = rTensorLinearEquiv (S := S) p := by
  rw [← AlgHom.toLinearMap_apply, rTensorAlgHom_toLinearMap]
  rfl

/-- The alg equiv from the tensor product of a polynomial ring and an algebra
  to a polynomial ring -/
noncomputable def rTensorAlgEquiv :
    (Polynomial S) ⊗[R] N ≃ₐ[S] Polynomial (S ⊗[R] N) := by
  apply AlgEquiv.ofLinearEquiv
    (rTensorLinearEquiv : Polynomial S ⊗[R] N ≃ₗ[S] Polynomial (S ⊗[R] N))
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
  rTensorAlgEquiv.trans (mapAlgEquiv (Algebra.TensorProduct.lid R N))

end Polynomial

end Algebra
