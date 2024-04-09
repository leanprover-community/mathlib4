/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.RingTheory.TensorProduct.Basic
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

variable {α R M N P : Type*}

/- section Finsupp

variable [DecidableEq α]
namespace Finsupp

lemma apply_single [AddCommMonoid N] [AddCommMonoid P]
    (e : N →+ P) (a : α) (n : N) (b : α) :
    e ((single a n) b) = single a (e n) b := by
  simp only [single_apply]
  split_ifs; rfl; exact map_zero e

lemma mapRange.addMonoidHom_apply_single
    [AddCommMonoid N] [AddCommMonoid P] (e : N →+ P) (a : α) (n : N) :
    mapRange.addMonoidHom e (single a n) = single a (e n) := by
    simp only [addMonoidHom_apply, mapRange_single]

#find_home! Finsupp.apply_single
#find_home! Finsupp.mapRange.addMonoidHom_apply_single
end Finsupp

end Finsupp
-/

section Functoriality

namespace MonoidAlgebra

variable [DecidableEq α]

open Finsupp

variable [Semiring N] [Semiring P]

lemma apply_single
    (e : N →+ P) (a : α) (n : N) (b : α) :
    e ((single a n) b) = single a (e n) b :=
  Finsupp.apply_single e a n b

/-- RingHom functoriality for the monoid algebra -/
noncomputable def ringHom [MulOneClass α] (e : N →+* P) :
    MonoidAlgebra N α →+* MonoidAlgebra P α := {
    mapRange.addMonoidHom e with
    map_one' := ext (fun _ => by simp [one_def])
    map_mul' := fun x y => ext (fun a => by
      simp only [mapRange.addMonoidHom_toZeroHom, ZeroHom.toFun_eq_coe,
        mapRange.zeroHom_apply, AddMonoidHom.toZeroHom_coe, AddMonoidHom.coe_coe]
      simp only [mapRange_apply]
      simp only [mul_def]
      rw [sum_apply, map_finsupp_sum, sum_apply]
      rw [sum_mapRange_index (by simp)]
      apply sum_congr
      intro b _
      rw [sum_apply, map_finsupp_sum, sum_mapRange_index (by simp), sum_apply]
      apply sum_congr
      intro c _
      rw [← _root_.map_mul]
      exact apply_single e.toAddMonoidHom (b * c) _ a) }

lemma ringHom_apply [MulOneClass α] (e : N →+* P) (x : MonoidAlgebra N α) :
    ringHom e x = mapRange.addMonoidHom e.toAddMonoidHom x :=
  rfl

lemma ringHom_apply_single [MulOneClass α] (e : N →+* P) (a  : α) (n : N) :
    ringHom e (single a n) = single a (e n) :=
  mapRange.addMonoidHom_apply_single e.toAddMonoidHom a n

/-- RingHom functoriality for the monoid algebra (equivalence) -/
noncomputable def equivRingHom [MulOneClass α] (e : N ≃+* P) :
    MonoidAlgebra N α ≃+* MonoidAlgebra P α := {
  mapRange.addEquiv e.toAddEquiv with
  map_mul' := (ringHom e.toRingHom).map_mul' }

/-- LinearMap functoriality for the monoid algebra -/
noncomputable def linearMap [Semiring R] [Module R N] [Module R P] (e : N →ₗ[R] P) :
    MonoidAlgebra N α →ₗ[R] MonoidAlgebra P α := {
  mapRange.linearMap e with
  toFun := mapRange.addMonoidHom e.toAddMonoidHom }

variable [Monoid α] [CommSemiring R] [Algebra R N] [Algebra R P]

/-- AlgHom functoriality for the monoid algebra -/
noncomputable def algHom (e : N →ₐ[R] P) :
    MonoidAlgebra N α →ₐ[R] MonoidAlgebra P α := {
  ringHom e.toRingHom with
  toFun := mapRange.addMonoidHom e.toAddMonoidHom
  commutes' := fun r => by
    simp only [AlgHom.toRingHom_eq_coe, RingHom.toAddMonoidHom_eq_coe, coe_algebraMap,
      Function.comp_apply, mapRange.addMonoidHom_apply, AddMonoidHom.coe_coe,
      RingHom.coe_coe, mapRange_single, AlgHom.commutes] }

lemma algHom_apply_apply (e : N →ₐ[R] P) (x : MonoidAlgebra N α) (a : α) :
    (algHom e) x a = e (x a) := by
  simp [algHom]

lemma algHom_apply_single (e : N →ₐ[R] P) (a : α) (n : N) :
    algHom e (single a n) = single a (e n) := by
  simp [algHom]

/-- The alg equiv of monoid algebras induced by an alg equiv between their coefficients. -/
noncomputable def algEquiv (e : N ≃ₐ[R] P) :
    MonoidAlgebra N α ≃ₐ[R] MonoidAlgebra P α := {
  mapRange.linearEquiv e.toLinearEquiv,
  algHom e.toAlgHom with }

end MonoidAlgebra

end Functoriality

section TensorProduct

open TensorProduct

variable [Monoid α] [DecidableEq α]
variable [CommSemiring R]
variable {S : Type*} [CommSemiring S] [Algebra R S]
variable [Semiring M] [Algebra R M] [Algebra S M] [IsScalarTower R S M]
variable  [Semiring N] [Algebra R N]

namespace MonoidAlgebra

open Finsupp

/-- AlgHom for the tensor product of the monoid algebra with an algebra -/
noncomputable def rTensorAlgHom :
    (MonoidAlgebra M α) ⊗[R] N →ₐ[S] MonoidAlgebra (M ⊗[R] N) α :=
  Algebra.TensorProduct.lift
    (algHom Algebra.TensorProduct.includeLeft)
    (singleOneAlgHom.comp Algebra.TensorProduct.includeRight)
    (fun x n => by
      simp only [AlgHom.coe_comp, Function.comp_apply, Algebra.TensorProduct.includeRight_apply,
        singleOneAlgHom_apply, commute_iff_eq]
      apply Finsupp.ext
      intro a
      rw [mul_def, sum_apply]
      erw [sum_apply, sum_single_index (by simp), sum_apply]
      apply sum_congr
      · intro b _
        rw [sum_apply, sum_single_index (by simp)]
        simp only [mul_one, single_apply, one_mul]
        split_ifs; simp [algHom_apply_apply]; rfl)

lemma rTensorAlgHom_apply_tmul_apply
    (x : MonoidAlgebra M α) (n : N) (a : α) :
    rTensorAlgHom (S := S) (x ⊗ₜ[R] n) a = (x a) ⊗ₜ[R] n := by
  simp only [rTensorAlgHom]
  simp only [Algebra.TensorProduct.lift_tmul]
  rw [AlgHom.comp_apply, singleOneAlgHom_apply, mul_single_one_apply]
  simp only [Algebra.TensorProduct.includeRight_apply]
  simp only [algHom_apply_apply, Algebra.TensorProduct.includeLeft_apply]
  simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

lemma rTensorAlgHom_toLinearMap :
    (rTensorAlgHom :
      MonoidAlgebra M α ⊗[R] N →ₐ[S] MonoidAlgebra (M ⊗[R] N) α).toLinearMap =
      (finsuppLeft' _ _ _ _ _).toLinearMap := by
  ext x n
  dsimp only [AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
    LinearMap.coe_restrictScalars, AlgHom.toLinearMap_apply]
  apply Finsupp.ext
  intro a
  rw [rTensorAlgHom_apply_tmul_apply, ← finsuppLeft_apply_tmul_apply]
  rfl

lemma rTensorAlgHom_toLinearMap' :
    (rTensorAlgHom :
      MonoidAlgebra M α ⊗[R] N →ₐ[R] MonoidAlgebra (M ⊗[R] N) α).toLinearMap =
      (finsuppLeft _ _ _ _).toLinearMap := by
  rw [rTensorAlgHom_toLinearMap]
  rfl

lemma rTensorAlgHom_apply_eq (x : MonoidAlgebra M α ⊗[R] N) :
    rTensorAlgHom (S := S) x = finsuppLeft' _ _ _ _ S x := by
  rw [← AlgHom.toLinearMap_apply, rTensorAlgHom_toLinearMap]
  rfl

/-- AlgHom equiv for the tensor product of the monoid algebra with an algebra -/
noncomputable def rTensorAlgEquiv :
    (MonoidAlgebra M α) ⊗[R] N ≃ₐ[S] MonoidAlgebra (M ⊗[R] N) α := by
  apply AlgEquiv.ofLinearEquiv
    (TensorProduct.finsuppLeft' R M N α S :
      MonoidAlgebra M α ⊗[R] N ≃ₗ[S] (MonoidAlgebra (M ⊗[R] N) α))
  · simp only [Algebra.TensorProduct.one_def]
    apply symm
    rw [← LinearEquiv.symm_apply_eq]
    simp only [one_def]
    apply finsuppLeft_symm_apply_single
  · intro x y
    erw [← rTensorAlgHom_apply_eq (S := S)]
    simp only [_root_.map_mul, rTensorAlgHom_apply_eq]
    rfl

lemma rTensorAlgEquiv_apply_eq (x : MonoidAlgebra M α ⊗[R] N) :
    rTensorAlgEquiv (S := S) x = finsuppLeft R M N α x :=
  rfl

lemma rTensorAlgEquiv_apply_tmul_apply
    (x : MonoidAlgebra M α) (n : N) (a : α) :
    rTensorAlgEquiv (S := S) (x ⊗ₜ[R] n) a = (x a) ⊗ₜ[R] n := by
  rw [rTensorAlgEquiv_apply_eq, finsuppLeft_apply_tmul_apply]

/-- AlgHom equiv for the tensor product of the monoid algebra with a module -/
noncomputable def scalarRTensorAlgEquiv :
    (MonoidAlgebra R α) ⊗[R] N ≃ₐ[R] MonoidAlgebra N α :=
  rTensorAlgEquiv.trans (algEquiv (Algebra.TensorProduct.lid R N))

end MonoidAlgebra

end TensorProduct
