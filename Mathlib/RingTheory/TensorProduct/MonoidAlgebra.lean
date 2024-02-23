/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.Data.MvPolynomial.Basic
import Mathlib.RingTheory.TensorProduct
import Mathlib.Algebra.Algebra.Equiv

/-! # TensorProduct of a monoid algebra

This file consists of three sections, the first two will have to be moved
somewhere else.

## two lemmas about `Finsupp.single`

## functoriality for `MonoidAlgebra`

We prove some functoriality definitions for the `Semiring` variable.
It remains to prove that this is a functor.

## tensor product

* `MonoidAlgebra.rTensorAlgEquiv`, the tensor product of
   `MonoidAlgebra M α` with `N` is `R`-linearly equivalent to `MonoidAlgebra (M ⊗[R] N) α`

* `MonoidAlgebra.scalarRTensorAlgEquiv`, the tensor product of
   `MonoidAlgebra R α` with `N` is `R`-linearly equivalent to `MonoidAlgebra N α`

## TODO

* State and prove functoriality properties

* Prove the `lTensor` variants

* Combine both to get that the tensor product of `MonoidAlgebra M α`
  with `MonoidAlgebra N β` is `R`-linearly equivalent to
  `MonoidAlgebra (M ⊗[R] N) (α × β)`.
-/
open TensorProduct

variable {α : Type*} [Monoid α] [DecidableEq α]
  {R : Type*} [CommSemiring R]
  {M N P : Type*}

section Finsupp

lemma Finsupp.apply_single [AddCommMonoid N] [AddCommMonoid P]
    (e : N →+ P) (a : α) (n : N) (b : α) :
    e ((Finsupp.single a n) b) = Finsupp.single a (e n) b := by
  simp only [Finsupp.single_apply]
  split_ifs with h
  · exact rfl
  · exact map_zero e

lemma Finsupp.mapRange.addMonoidHom_apply_single
    [AddCommMonoid N] [AddCommMonoid P] (e : N →+ P) (a : α) (n : N) :
    Finsupp.mapRange.addMonoidHom e (Finsupp.single a n) = Finsupp.single a (e n) := by
    ext b
    apply Finsupp.apply_single

end Finsupp

section MonoidAlgebraFunctoriality

variable [Semiring N] [Semiring P]

/- noncomputable example
    {P : Type*} [Semiring P] [Algebra R P] (e : N ≃ₗ[R] P) :
    MonoidAlgebra N α ≃ₗ[R] MonoidAlgebra P α :=
  Finsupp.mapRange.linearEquiv e -/

lemma MonoidAlgebra.apply_single
    (e : N →+ P) (a : α) (n : N) (b : α) :
    e ((MonoidAlgebra.single a n) b) = MonoidAlgebra.single a (e n) b :=
  Finsupp.apply_single e a n b

/-- RingHom functoriality for the monoid algebra -/
noncomputable def MonoidAlgebra.ringHom (e : N →+* P) :
    MonoidAlgebra N α →+* MonoidAlgebra P α := {
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
      rw [Finsupp.sum_apply, map_finsupp_sum,
        Finsupp.sum_mapRange_index (by simp), Finsupp.sum_apply]
      apply Finsupp.sum_congr
      intro c _
      have := MonoidAlgebra.apply_single e.toAddMonoidHom (b * c) (x b * y c) a
      simp only [RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, _root_.map_mul] at this
      rw [← _root_.map_mul]
      exact MonoidAlgebra.apply_single e.toAddMonoidHom (b * c) _ a) }

lemma MonoidAlgebra.ringHom_apply (e : N →+* P) (x : MonoidAlgebra N α) :
    MonoidAlgebra.ringHom e x = Finsupp.mapRange.addMonoidHom e.toAddMonoidHom x :=
  rfl

lemma MonoidAlgebra.ringHom_apply_single (e : N →+* P) (a  : α) (n : N) :
    MonoidAlgebra.ringHom e (single a n) = single a (e n) :=
  Finsupp.mapRange.addMonoidHom_apply_single e.toAddMonoidHom a n

/-- RingHom functoriality for the monoid algebra (equivalence) -/
noncomputable def MonoidAlgebra.equivRingHom (e : N ≃+* P) :
    MonoidAlgebra N α ≃+* MonoidAlgebra P α := {
  Finsupp.mapRange.addEquiv e.toAddEquiv with
  map_mul' := (MonoidAlgebra.ringHom e.toRingHom).map_mul' }

/-- LinearMap functoriality for the monoid algebra -/
noncomputable def MonoidAlgebra.linearMap [Module R N] [Module R P] (e : N →ₗ[R] P) :
    MonoidAlgebra N α →ₗ[R] MonoidAlgebra P α := {
  Finsupp.mapRange.linearMap e with
  toFun := Finsupp.mapRange.addMonoidHom e.toAddMonoidHom }

/-- AlgHom functoriality for the monoid algebra -/
noncomputable def MonoidAlgebra.algHom [Algebra R N] [Algebra R P] (e : N →ₐ[R] P) :
    MonoidAlgebra N α →ₐ[R] MonoidAlgebra P α := {
  MonoidAlgebra.ringHom e.toRingHom with
  toFun := Finsupp.mapRange.addMonoidHom e.toAddMonoidHom
  commutes' := fun r => by
    simp only [AlgHom.toRingHom_eq_coe, RingHom.toAddMonoidHom_eq_coe, coe_algebraMap,
      Function.comp_apply, Finsupp.mapRange.addMonoidHom_apply, AddMonoidHom.coe_coe,
      RingHom.coe_coe, Finsupp.mapRange_single, AlgHom.commutes] }

noncomputable def MonoidAlgebra.algEquiv [Algebra R N] [Algebra R P] (e : N ≃ₐ[R] P) :
    MonoidAlgebra N α ≃ₐ[R] MonoidAlgebra P α := {
  Finsupp.mapRange.linearEquiv e.toLinearEquiv,
  MonoidAlgebra.algHom e.toAlgHom with }

end MonoidAlgebraFunctoriality

section MonoidAlgebra.TensorProduct

variable [Semiring M] [Algebra R M] [Semiring N] [Algebra R N]

/-- Linear equiv for the tensor product of the monoid algebra with an algebra -/
noncomputable def MonoidAlgebra.rTensorLinearEquiv :
    (MonoidAlgebra M α) ⊗[R] N ≃ₗ[R] MonoidAlgebra (M ⊗[R] N) α :=
  TensorProduct.finsuppLeft

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

/-- AlgHom equiv for the tensor product of the monoid algebra with an algebra -/
noncomputable def MonoidAlgebra.rTensorAlgEquiv :
    (MonoidAlgebra M α) ⊗[R] N ≃ₐ[R] MonoidAlgebra (M ⊗[R] N) α := by
  apply AlgEquiv.ofLinearEquiv TensorProduct.finsuppLeft
  · simp only [Algebra.TensorProduct.one_def]
    apply symm
    rw [← LinearEquiv.symm_apply_eq]
    simp only [MonoidAlgebra.one_def]
    apply finsuppLeft_symm_apply_single
  · exact MonoidAlgebra.rTensorLinearEquiv_mul

/-- AlgHom equiv for the tensor product of the monoid algebra with a module -/
noncomputable def MonoidAlgebra.scalarRTensorAlgEquiv :
    (MonoidAlgebra R α) ⊗[R] N ≃ₐ[R] MonoidAlgebra N α :=
  MonoidAlgebra.rTensorAlgEquiv.trans (MonoidAlgebra.algEquiv (Algebra.TensorProduct.lid R N))
