/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

-- import Mathlib.Data.Polynomial.Basic
import Mathlib.Data.Polynomial.AlgebraMap
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.RingTheory.TensorProduct

/-! # Tensor products of a polynomial ring

Adaptations of `TensorProduct.finsuppLeft` when the `Finsupp` is a `Polynomial`.

It is messy because `Polynomial` is not a `Finsupp`…
I believe most of this file should go elsewhere,
and maybe the small stuff that remains could be deleted.

TODO : use what has been done for monoid algebras to get alg hom equiv
(or do it directly)

-/
open TensorProduct LinearMap

universe u v w

variable {R : Type u} {M : Type v} {N : Type w}
  [CommSemiring R] [AddCommMonoid M] [Module R M]

variable {S : Type*} [CommSemiring S] [Algebra R S]

section Module

variable [AddCommMonoid N] [Module R N]

-- keep ?
noncomputable def LinearEquiv.rTensor
    (P : Type*) (e : M ≃ₗ[R] N)  [AddCommMonoid P] [Module R P] :
    M ⊗[R] P ≃ₗ[R] N ⊗[R] P := TensorProduct.congr e (refl R P)

-- TODO : lTensor ?


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

lemma TensorProduct.congr_isLinearMap'
    [Module S M] [IsScalarTower R S M] [Module S N] [IsScalarTower R S N]
    {P : Type*} [AddCommMonoid P] [Module R P]
    {Q : Type*} [AddCommMonoid Q] [Module R Q]
    (e : M ≃ₗ[S] N) (f : P ≃ₗ[R] Q) :
    IsLinearMap S (TensorProduct.congr (e.restrictScalars R) f) :=
  TensorProduct.map_isLinearMap' e.toLinearMap f.toLinearMap

lemma LinearEquiv.rTensor_isLinearMap'
    [Module S M] [IsScalarTower R S M] [Module S N] [IsScalarTower R S N]
    (P : Type*) [AddCommMonoid P] [Module R P] (e : M ≃ₗ[S] N) :
    IsLinearMap S (LinearEquiv.rTensor P (e.restrictScalars R)) :=
  TensorProduct.map_isLinearMap' e.toLinearMap _

noncomputable def LinearEquiv.rTensor'
    [Module S M] [IsScalarTower R S M] [Module S N] [IsScalarTower R S N]
    (P : Type*) [AddCommMonoid P] [Module R P] (e : M ≃ₗ[S] N) :
    M ⊗[R] P ≃ₗ[S] N ⊗[R] P := {
  (LinearEquiv.rTensor P (e.restrictScalars R)) with
  map_smul' := (LinearEquiv.rTensor_isLinearMap' P e).map_smul }

lemma LinearEquiv.rTensor'_apply
    [Module S M] [IsScalarTower R S M] [Module S N] [IsScalarTower R S N]
    (P : Type*) [AddCommMonoid P] [Module R P] (e : M ≃ₗ[S] N)
    (mp : M ⊗[R] P) :
    LinearEquiv.rTensor' P e mp = LinearEquiv.rTensor P (e.restrictScalars R) mp := rfl

open Polynomial

def Polynomial.toFinsuppLinearEquiv : S[X] ≃ₗ[S] (ℕ →₀ S) := {
  Polynomial.toFinsuppIso S  with
  map_smul' := fun r p => by simp }

noncomputable def Polynomial.rTensor :
    Polynomial R ⊗[R] N ≃ₗ[R] ℕ →₀ N :=
  (LinearEquiv.rTensor N Polynomial.toFinsuppLinearEquiv).trans TensorProduct.finsuppScalarLeft

lemma Polynomial.rTensor_apply_tmul_apply (p : Polynomial R) (n : N) (i : ℕ) :
    Polynomial.rTensor (p ⊗ₜ[R] n) i = (coeff p i) • n := by
  simp only [rTensor, LinearEquiv.trans_apply]
  simp only [LinearEquiv.rTensor, congr_tmul, LinearEquiv.refl_apply]
  rw [finsuppScalarLeft_apply_tmul_apply _ n i]
  rfl

lemma Polynomial.rTensor_apply_tmul (p : Polynomial R) (n : N) :
    Polynomial.rTensor (p ⊗ₜ[R] n) = p.sum (fun i r => Finsupp.single i (r • n)) := by
  ext i
  rw [Polynomial.rTensor_apply_tmul_apply]
  rw [Polynomial.sum_def]
  rw [Finset.sum_apply']
  rw [Finset.sum_eq_single i]
  · simp only [Finsupp.single_eq_same]
  · exact fun _ _ => Finsupp.single_eq_of_ne
  · intro h
    simp only [mem_support_iff, ne_eq, not_not] at h
    rw [h, zero_smul, Finsupp.single_zero, Finsupp.coe_zero, Pi.zero_apply]

noncomputable def Polynomial.rTensor' :
    Polynomial S ⊗[R] N ≃ₗ[S] ℕ →₀ (S ⊗[R] N) :=
  (LinearEquiv.rTensor' N Polynomial.toFinsuppLinearEquiv).trans TensorProduct.finsuppLeft'

lemma Polynomial.rTensor'_apply_tmul_apply (p : Polynomial S) (n : N) (i : ℕ) :
    Polynomial.rTensor' (p ⊗ₜ[R] n) i = (coeff p i) ⊗ₜ[R] n := by
  simp only [rTensor', LinearEquiv.trans_apply, finsuppLeft'_apply]
  simp only [LinearEquiv.rTensor'_apply, LinearEquiv.rTensor, congr_tmul,
    LinearEquiv.restrictScalars_apply, LinearEquiv.refl_apply]
  simp only [toFinsuppLinearEquiv, RingEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe,
    Equiv.invFun_as_coe, LinearEquiv.coe_mk, toFinsuppIso_apply]
  rw [finsuppLeft_apply_tmul_apply]
  rfl

end Module

section Algebra

variable [CommSemiring N] [Algebra R N]

noncomputable def Polynomial.rTensorAlgHom :
    (Polynomial S) ⊗[R] N →ₐ[S] Polynomial (S ⊗[R] N) :=
  Algebra.TensorProduct.lift
    (Polynomial.aeval Polynomial.X)
    ((IsScalarTower.toAlgHom R (S ⊗[R] N) _).comp Algebra.TensorProduct.includeRight)
    (fun p n => by simp only [commute_iff_eq, mul_comm])

noncomputable def Polynomial.scalarRTensorAlgHom :
    Polynomial R ⊗[R] N →ₐ[R] Polynomial N :=
  Algebra.TensorProduct.lift
    (aeval Polynomial.X)
    (IsScalarTower.toAlgHom R N _)
    (fun p n => by simp [commute_iff_eq, mul_comm])
