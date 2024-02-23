/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.Data.MvPolynomial.Basic
import Mathlib.RingTheory.TensorProduct
import Mathlib.Algebra.Algebra.Equiv

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

noncomputable example
    {N' : Type*} [Semiring N'] [Algebra R N'] (e : N ≃ₗ[R] N') :
    MonoidAlgebra N α ≃ₗ[R] MonoidAlgebra N' α :=
  Finsupp.mapRange.linearEquiv e

lemma Finsupp.apply_single
    {N N' : Type*} [AddCommMonoid N] [AddCommMonoid N']
    (e : N →+ N') (a : α) (n : N) (b : α) :
    e ((Finsupp.single a n) b) = Finsupp.single a (e n) b := by
  simp only [Finsupp.single_apply]
  split_ifs with h
  · exact rfl
  · exact map_zero e

lemma Finsupp.mapRange.addMonoidHom_apply_single
    {N N' : Type*} [AddCommMonoid N] [AddCommMonoid N']
    (e : N →+ N') (a : α) (n : N) :
    Finsupp.mapRange.addMonoidHom e (Finsupp.single a n) = Finsupp.single a (e n) := by
    ext b
    apply Finsupp.apply_single

lemma MonoidAlgebra.apply_single
    {N N' : Type*} [Semiring N] [Semiring N']
    (e : N →+ N') (a : α) (n : N) (b : α) :
    e ((MonoidAlgebra.single a n) b) = MonoidAlgebra.single a (e n) b :=
  Finsupp.apply_single e a n b

noncomputable def MonoidAlgebra.ringHom
    {N N' : Type*} [Semiring N] [Semiring N'] (e : N →+* N') :
    MonoidAlgebra N α →+* MonoidAlgebra N' α := {
    Finsupp.mapRange.addMonoidHom e with
    map_one' := Finsupp.ext (fun _ => by simp [MonoidAlgebra.one_def])
    map_mul' := fun x y => Finsupp.ext (fun a => by
      simp only [Finsupp.mapRange.addMonoidHom_toZeroHom, ZeroHom.toFun_eq_coe,
        Finsupp.mapRange.zeroHom_apply, AddMonoidHom.toZeroHom_coe, AddMonoidHom.coe_coe]
      simp only [Finsupp.mapRange_apply]
      simp only [MonoidAlgebra.mul_def]
      rw [Finsupp.sum_apply, map_finsupp_sum, Finsupp.sum_apply]
      rw [Finsupp.sum_mapRange_index (by simp)]
      apply Finsupp.sum_congr
      intro b _
      rw [Finsupp.sum_apply, map_finsupp_sum, Finsupp.sum_mapRange_index (by simp), Finsupp.sum_apply]
      apply Finsupp.sum_congr
      intro c _
      have := MonoidAlgebra.apply_single e.toAddMonoidHom (b * c) (x b * y c) a
      simp only [RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, _root_.map_mul] at this
      rw [← _root_.map_mul]
      exact MonoidAlgebra.apply_single e.toAddMonoidHom (b * c) _ a) }

lemma MonoidAlgebra.ringHom_apply
    {N' : Type*} [Semiring N'] (e : N →+* N') (x : MonoidAlgebra N α) :
    MonoidAlgebra.ringHom e x = Finsupp.mapRange.addMonoidHom e.toAddMonoidHom x :=
  rfl

lemma MonoidAlgebra.ringHom_apply_single
    {N' : Type*} [Semiring N'] (e : N →+* N') (a  : α) (n : N) :
    MonoidAlgebra.ringHom e (single a n) = single a (e n) :=
  Finsupp.mapRange.addMonoidHom_apply_single e.toAddMonoidHom a n

noncomputable def MonoidAlgebra.equivRingHom
    {N' : Type*} [Semiring N'] (e : N ≃+* N') :
    MonoidAlgebra N α ≃+* MonoidAlgebra N' α := {
  Finsupp.mapRange.addEquiv e.toAddEquiv with
  map_mul' := (MonoidAlgebra.ringHom e.toRingHom).map_mul' }

noncomputable def MonoidAlgebra.linearMap
    {N' : Type*} [Semiring N'] [Algebra R N'] (e : N →ₗ[R] N') :
    MonoidAlgebra N α →ₗ[R] MonoidAlgebra N' α := {
  Finsupp.mapRange.linearMap e with
  toFun := Finsupp.mapRange.addMonoidHom e.toAddMonoidHom }

noncomputable def MonoidAlgebra.algHom
    {N' : Type*} [Semiring N'] [Algebra R N'] (e : N →ₐ[R] N') :
    MonoidAlgebra N α →ₐ[R] MonoidAlgebra N' α := {
  MonoidAlgebra.ringHom e.toRingHom with
  toFun := Finsupp.mapRange.addMonoidHom e.toAddMonoidHom
  commutes' := fun r => by
    simp only [AlgHom.toRingHom_eq_coe, RingHom.toAddMonoidHom_eq_coe, coe_algebraMap,
      Function.comp_apply, Finsupp.mapRange.addMonoidHom_apply, AddMonoidHom.coe_coe,
      RingHom.coe_coe, Finsupp.mapRange_single, AlgHom.commutes] }

noncomputable def MonoidAlgebra.algEquiv
    {N' : Type*} [Semiring N'] [Algebra R N'] (e : N ≃ₐ[R] N') :
    MonoidAlgebra N α ≃ₐ[R] MonoidAlgebra N' α := {
  Finsupp.mapRange.linearEquiv e.toLinearEquiv,
  MonoidAlgebra.algHom e.toAlgHom with }

noncomputable def MonoidAlgebra.rTensorLinearEquiv
    {M : Type*} [Semiring M] [Algebra R M] :
    (MonoidAlgebra M α) ⊗[R] N ≃ₗ[R] MonoidAlgebra (M ⊗[R] N) α :=
  TensorProduct.finsuppLeft

variable {M : Type*} [Semiring M] [Algebra R M]

lemma MonoidAlgebra.rTensorLinearEquiv_of_tmul (a : α) (n : N) :
    MonoidAlgebra.rTensorLinearEquiv ((MonoidAlgebra.of M α) a ⊗ₜ[R] n)
    = (MonoidAlgebra.of (M ⊗[R] N) α a) *
        (MonoidAlgebra.single 1 (1 ⊗ₜ[R] n)):= by
  unfold MonoidAlgebra.rTensorLinearEquiv
  apply Finsupp.ext
  intro x
  erw [finsuppLeft_apply_tmul_apply]
  simp only [MonoidAlgebra.of_apply]
  simp only [MonoidAlgebra.single_mul_single, mul_one, one_mul]
  simp only [MonoidAlgebra.single_apply]
  split_ifs with h
  · rfl
  · simp only [zero_tmul]

lemma MonoidAlgebra.rTensorLinearEquiv_mul (x y : (MonoidAlgebra M α) ⊗[R] N) :
    MonoidAlgebra.rTensorLinearEquiv (x * y) =
    MonoidAlgebra.rTensorLinearEquiv x * MonoidAlgebra.rTensorLinearEquiv y := by
  unfold MonoidAlgebra.rTensorLinearEquiv
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [add_mul, map_add, hx, hy]
  | tmul p m =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [mul_add, map_add, hx, hy]
    | tmul q n =>
      simp only [Algebra.TensorProduct.tmul_mul_tmul]
      apply Finsupp.ext
      intro a
      erw [finsuppLeft_apply_tmul_apply]
      rw [MonoidAlgebra.mul_def, Finsupp.sum_apply, MonoidAlgebra.mul_def, Finsupp.sum_apply]
      erw [finsuppLeft_apply_tmul]
      rw [Finsupp.sum_sum_index (by simp), Finsupp.sum, TensorProduct.sum_tmul]
      conv_rhs => rw [Finsupp.sum]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finsupp.sum_apply, Finsupp.sum, TensorProduct.sum_tmul,
        Finsupp.sum_single_index (by simp), Finsupp.sum_apply]
      erw [finsuppLeft_apply_tmul]
      rw [Finsupp.sum_sum_index (by simp), Finsupp.sum]
      apply Finset.sum_congr rfl
      intro y _
      rw [Finsupp.sum_single_index (by simp)]
      by_cases h : x * y = a
      · simp only [h, Finsupp.single_eq_same, Algebra.TensorProduct.tmul_mul_tmul]
      · simp only [Finsupp.single_eq_of_ne h, zero_tmul]
      -- remaining assumptions of `Finsupp.sum_single_index`
      · intro b y z
        simp [mul_add, tmul_add]
      · intro b y z
        simp_rw [add_mul, MonoidAlgebra.single_add, Finsupp.sum_add]
        exact rfl

noncomputable def MonoidAlgebra.rTensorAlgEquiv :
    (MonoidAlgebra M α) ⊗[R] N ≃ₐ[R] MonoidAlgebra (M ⊗[R] N) α := by
  apply AlgEquiv.ofLinearEquiv TensorProduct.finsuppLeft
  · simp only [Algebra.TensorProduct.one_def]
    apply symm
    rw [← LinearEquiv.symm_apply_eq]
    simp only [MonoidAlgebra.one_def]
    apply finsuppLeft_symm_apply_single
  · exact MonoidAlgebra.rTensorLinearEquiv_mul

noncomputable def MonoidAlgebra.scalarRTensorAlgEquiv :
    (MonoidAlgebra R α) ⊗[R] N ≃ₐ[R] MonoidAlgebra N α :=
  MonoidAlgebra.rTensorAlgEquiv.trans (MonoidAlgebra.algEquiv (Algebra.TensorProduct.lid R N))
