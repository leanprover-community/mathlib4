/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Data.Finsupp.Defs

/-! # TensorProduct of a monoid algebra

This file consists of two sections, the first one will have to be moved
somewhere else.

## functoriality for `MonoidAlgebra`

We prove some functoriality definitions for the `Semiring` variable.

## tensor product

* `MonoidAlgebra.rTensorAlgEquiv`, the tensor product of
   `MonoidAlgebra M α` with `N` is `R`-linearly equivalent to `MonoidAlgebra (M ⊗[R] N) α`

* `MonoidAlgebra.scalarRTensorAlgEquiv`, the tensor product of
   `MonoidAlgebra R α` with `N` is `R`-linearly equivalent to `MonoidAlgebra N α`

## TODO

* Prove the `lTensor` variants

* Combine both to get that the tensor product of `MonoidAlgebra M α`
  with `MonoidAlgebra N β` is `R`-linearly equivalent to
  `MonoidAlgebra (M ⊗[R] N) (α × β)`.
-/

variable {α R M N P : Type*}

/-
section Functoriality

namespace MonoidAlgebra

variable [DecidableEq α]

open Finsupp

variable [Semiring N] [Semiring P]

lemma apply_single (e : N →+ P) (a : α) (n : N) (b : α) :
    e ((single a n) b) = single a (e n) b :=
  Finsupp.apply_single (e : N →+ P) a n b

/-- AddHom functoriality for the monoid algebra -/
noncomputable def addHom [MulOneClass α] (e : N →+ P) :
    MonoidAlgebra N α →+ MonoidAlgebra P α :=
  liftNC ((Finsupp.singleAddHom 1).comp e) (of P α)

-- variant using Finsupp.mapRange.AddMonoidHom
noncomputable def addHom' (e : N →+ P) :
    MonoidAlgebra N α →+ MonoidAlgebra P α :=
  Finsupp.mapRange.addMonoidHom e

@[simp]
lemma addHom_single [MulOneClass α] (e : N →+ P) (a  : α) (n : N) :
    addHom e (single a n) = single a (e n) := by
  simp only [addHom, liftNC_single, of_apply]
  convert MonoidAlgebra.single_mul_single <;> simp only [one_mul, mul_one]

lemma addHom'_apply [MulOneClass α] (e : N →+ P) (x : MonoidAlgebra N α) :
    addHom' e x = mapRange ⇑e e.map_zero x :=
  mapRange.addMonoidHom_apply _ _

@[simp]
lemma addHom'_single [MulOneClass α] (e : N →+ P) (a  : α) (n : N) :
    addHom' e (single a n) = single a (e n) := by
  rw [addHom'_apply, mapRange_single]

lemma addHom_apply [MulOneClass α] (e : N →+ P) (x : MonoidAlgebra N α) :
    addHom e x = mapRange.addMonoidHom e x := by
  rw [← MonoidAlgebra.sum_single x]
  simp only [map_finsupp_sum]
  apply congr_arg
  ext a n
  simp only [addHom_single, RingHom.toAddMonoidHom_eq_coe,
    mapRange.addMonoidHom_apply, AddMonoidHom.coe_coe, mapRange_single]

theorem addHom_eq_addHom' [MulOneClass α] (e : N →+ P) :
    (addHom e : MonoidAlgebra N α →+ MonoidAlgebra P α) = addHom' e := by
  apply Finsupp.addHom_ext
  intro a n
  erw [addHom_single, addHom'_single]

lemma addHom_id [MulOneClass α] :
    (addHom (AddMonoidHom.id N) : MonoidAlgebra N α →+ MonoidAlgebra N α)
      = AddMonoidHom.id _ :=
  Finsupp.addHom_ext (addHom_single _)

lemma addHom'_id [MulOneClass α] :
    (addHom' (AddMonoidHom.id N) : MonoidAlgebra N α →+ MonoidAlgebra N α)
      = AddMonoidHom.id _ :=
  Finsupp.addHom_ext (addHom'_single _)

lemma addHom_comp [Semiring M] [MulOneClass α] (f : M →+ N) (e : N →+ P) :
    (addHom (e.comp f) : MonoidAlgebra M α →+ MonoidAlgebra P α)
      = (addHom e).comp (addHom f) := by
  apply Finsupp.addHom_ext
  intro a m
  simp only [AddMonoidHom.coe_comp, Function.comp_apply]
  erw [addHom_single, addHom_single f a m, addHom_single e a _]
  rfl

lemma addHom'_comp [Semiring M] [MulOneClass α] (f : M →+ N) (e : N →+ P) :
    (addHom' (e.comp f) : MonoidAlgebra M α →+ MonoidAlgebra P α)
      = (addHom' e).comp (addHom' f) := by
  apply Finsupp.addHom_ext
  intro a m
  simp only [AddMonoidHom.coe_comp, Function.comp_apply]
  erw [addHom'_single, addHom'_single f a m, addHom'_single e a]
  rfl

variable [Monoid α]
-- TODO : generalize to [MulOneClass α]

/-- RingHom functoriality for the monoid algebra (MulOneClass)-/
noncomputable def ringHom' {α : Type*} [MulOneClass α] (e : N →+* P) :
    MonoidAlgebra N α →+* MonoidAlgebra P α := {
  addHom' e.toAddMonoidHom with
  map_one' := by simp [one_def, addHom'_single]
  map_mul' := fun f g => by
    simp only [RingHom.toAddMonoidHom_eq_coe, ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe]
    rw [← MonoidAlgebra.sum_single f, ← MonoidAlgebra.sum_single g]
    simp only [Finsupp.mul_sum, map_finsupp_sum]
    apply congr_arg
    ext a m
    rw [Finsupp.sum_mul, map_finsupp_sum, Finsupp.sum_mul]
    simp only [single_mul_single, addHom'_single, AddMonoidHom.coe_coe, map_mul] }

-- if one uses Finsupp.mapRange.AddMonoidHom, multiplicativity requires a proof
/-- RingHom functoriality for the monoid algebra -/
noncomputable def ringHom (e : N →+* P) :
    MonoidAlgebra N α →+* MonoidAlgebra P α :=
  liftNCRingHom (singleOneRingHom.comp e) (of P α) (by
    intro n a
    simp only [commute_iff_eq, RingHom.coe_comp, Function.comp_apply,
      singleOneRingHom_apply, ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe,
      singleAddHom_apply, of_apply, single_mul_single, one_mul, mul_one])

@[simp]
lemma ringHom_single (e : N →+* P) (a  : α) (n : N) :
    ringHom e (single a n) = single a (e n) :=
  addHom_single e.toAddMonoidHom a n

lemma ringHom_apply (e : N →+* P) (x : MonoidAlgebra N α) :
    ringHom e x = mapRange.addMonoidHom e.toAddMonoidHom x :=
  addHom_apply e.toAddMonoidHom x

theorem ringHom_id :
    (ringHom (RingHom.id N) : MonoidAlgebra N α →+* MonoidAlgebra N α)
    = RingHom.id _ := by
  ext x <;> simp

theorem ringHom_comp [Semiring M] (f : M →+* N) (e : N →+* P) :
    ((ringHom e).comp (ringHom f) : MonoidAlgebra M α →+* MonoidAlgebra P α)
    = ringHom (e.comp f) := by
  ext x <;> simp

/-- RingHom functoriality for the monoid algebra (equivalence) -/
noncomputable def ringEquiv (e : N ≃+* P) :
    MonoidAlgebra N α ≃+* MonoidAlgebra P α := by
  apply RingEquiv.ofHomInv (ringHom e) (ringHom e.symm) <;>
  · convert ringHom_comp _ _
    convert ringHom_id.symm
    simp only [RingEquiv.symm_comp, RingEquiv.comp_symm]

-- This could be Finsupp.mapRange.linearMap
/-- LinearMap functoriality for the monoid algebra -/
noncomputable def linearMap [Semiring R] [Module R N] [Module R P] (e : N →ₗ[R] P) :
    MonoidAlgebra N α →ₗ[R] MonoidAlgebra P α := {
  addHom e.toAddMonoidHom  with
  map_smul' := fun r x ↦ by
    simp only [ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe, RingHom.id_apply]
    rw [← MonoidAlgebra.sum_single x]
    simp only [map_finsupp_sum, smul_sum]
    apply congr_arg
    ext a n
    rw [smul_single, addHom_single, addHom_single, smul_single]
    simp only [LinearMap.toAddMonoidHom_coe, LinearMapClass.map_smul] }

variable [CommSemiring R] [Algebra R N] [Algebra R P]

/-- AlgHom functoriality for the monoid algebra -/
noncomputable def algHom (e : N →ₐ[R] P) :
    MonoidAlgebra N α →ₐ[R] MonoidAlgebra P α := {
  ringHom e.toRingHom with
  commutes' := fun r => by
    simp only [AlgHom.toRingHom_eq_coe, RingHom.toMonoidHom_eq_coe, coe_algebraMap,
      Function.comp_apply, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, MonoidHom.coe_coe,
        ringHom_single, RingHom.coe_coe, AlgHom.commutes] }

@[simp]
lemma algHom_apply_apply (e : N →ₐ[R] P) (x : MonoidAlgebra N α) (a : α) :
    (algHom e) x a = e (x a) := by
  simp [algHom, ringHom_apply]

@[simp]
lemma algHom_apply_single (e : N →ₐ[R] P) (a : α) (n : N) :
    algHom e (single a n) = single a (e n) := by
  simp [algHom]

/-- The alg equiv of monoid algebras induced by an alg equiv between their coefficients. -/
noncomputable def algEquiv (e : N ≃ₐ[R] P) :
    MonoidAlgebra N α ≃ₐ[R] MonoidAlgebra P α := {
  ringEquiv e.toRingEquiv, algHom e.toAlgHom with }

end MonoidAlgebra

end Functoriality
-/
section

open MonoidAlgebra

variable {R S T α : Type*} [CommSemiring R] [Semiring S] [Semiring T]

/-- AddHom functoriality for the monoid algebra -/
noncomputable def addHom [MulOneClass α] (e : S →+ T) :
    MonoidAlgebra S α →+ MonoidAlgebra T α :=
  liftNC ((Finsupp.singleAddHom 1).comp e) (of T α)

variable [Monoid α]

/-- RingHom functoriality for the monoid algebra -/
noncomputable def ringHom (e : S →+* T) :
    MonoidAlgebra S α →+* MonoidAlgebra T α :=
  liftNCRingHom (singleOneRingHom.comp e) (of T α) (fun s a ↦ by
    simp only [RingHom.coe_comp, Function.comp_apply, singleOneRingHom_apply,
      ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe,
      Finsupp.singleAddHom_apply, of_apply, commute_iff_eq, single_mul_single,
      one_mul, mul_one])

/-- RingHom functoriality for the monoid algebra (equivalence) -/
noncomputable def ringEquiv (e : S ≃+* T) :
    MonoidAlgebra S α ≃+* MonoidAlgebra T α := by
  apply RingEquiv.ofHomInv (ringHom e) (ringHom e.symm) <;>
  · convert ringHom_comp _ _
    convert ringHom_id.symm
    simp only [RingEquiv.symm_comp, RingEquiv.comp_symm]

end
section TensorProduct

open TensorProduct Finsupp

variable [Monoid α] [DecidableEq α]
variable [CommSemiring R]
variable {S : Type*} [Semiring S] [Algebra R S]
variable [AddCommMonoid N] [Module R N]

-- variable {S : Type*} [CommSemiring S] [Algebra R S]
-- variable [Semiring M] [Algebra R M] [Algebra S M] [IsScalarTower R S M]
-- variable [Semiring N] [Algebra R N]

namespace MonoidAlgebra

section Module

/-- The tensor product of a monoid algebra by a module is
  linearly equivalent to a Finsupp of a tensor product -/
noncomputable def rTensor :
    MonoidAlgebra S α ⊗[R] N ≃ₗ[R] α →₀ (S ⊗[R] N) :=
  TensorProduct.finsuppLeft' _ _ _ _ _

lemma rTensor_apply_tmul (p : MonoidAlgebra S α) (n : N) :
    rTensor (p ⊗ₜ[R] n) = p.sum (fun i m ↦ Finsupp.single i (m ⊗ₜ[R] n)) :=
  TensorProduct.finsuppLeft_apply_tmul p n

lemma rTensor_apply_tmul_apply (p : MonoidAlgebra S α) (n : N) (a : α) :
    rTensor (p ⊗ₜ[R] n) a = (p a) ⊗ₜ[R] n :=
  TensorProduct.finsuppLeft_apply_tmul_apply p n a

lemma rTensor_apply_monomial_tmul (b : α) (s : S) (n : N) (a : α) :
    rTensor (single b s ⊗ₜ[R] n) a = if b = a then s ⊗ₜ[R] n else 0 := by
  simp only [rTensor_apply_tmul_apply, single_apply, ite_tmul]

lemma rTensor_apply (t : MonoidAlgebra S α ⊗[R] N) (a : α) :
    rTensor t a = LinearMap.rTensor N (lapply a) t :=
  TensorProduct.finsuppLeft_apply t a

@[simp]
lemma rTensor_symm_apply_single (a : α) (s : S) (n : N) :
    rTensor.symm (Finsupp.single a (s ⊗ₜ n)) = (single a s) ⊗ₜ[R] n :=
  TensorProduct.finsuppLeft_symm_apply_single a s n

/-- The tensor product of a monoid algebra by a module is
  linearly equivalent to a Finsupp of a tensor product -/
noncomputable def scalarRTensor :
    MonoidAlgebra R α ⊗[R] N ≃ₗ[R] α →₀ N :=
  TensorProduct.finsuppScalarLeft _ _ _

lemma scalarRTensor_apply_tmul (p : MonoidAlgebra R α) (n : N) :
    scalarRTensor (p ⊗ₜ[R] n) = p.sum (fun i r ↦ Finsupp.single i (r • n)) :=
  TensorProduct.finsuppScalarLeft_apply_tmul p n

lemma scalarRTensor_apply_tmul_apply (p : MonoidAlgebra R α) (n : N) (a : α) :
    scalarRTensor (p ⊗ₜ[R] n) a = (p a) • n :=
  TensorProduct.finsuppScalarLeft_apply_tmul_apply p n a

lemma scalarRTensor_apply_monomial_tmul (b : α) (r : R) (n : N) (a : α) :
    scalarRTensor (single b r ⊗ₜ[R] n) a = if b = a then r • n else 0 := by
  simp only [scalarRTensor_apply_tmul_apply, single_apply, ite_smul, zero_smul]

lemma scalarRTensor_apply (t : MonoidAlgebra R α ⊗[R] N) (a : α) :
    scalarRTensor t a = TensorProduct.lid R N (LinearMap.rTensor N (lapply a) t) :=
  finsuppScalarLeft_apply t a

@[simp]
lemma scalarRTensor_symm_apply_single (a : α) (n : N) :
    scalarRTensor.symm (Finsupp.single a n) = (single a 1) ⊗ₜ[R] n :=
  TensorProduct.finsuppScalarLeft_symm_apply_single a n

end Module

section Algebra

variable {T : Type*} [Semiring T] [Algebra R T]

/-- AlgHom for the tensor product of the monoid algebra with an algebra -/
noncomputable def rTensorAlgHom :
    (MonoidAlgebra S α) ⊗[R] T →ₐ[R] MonoidAlgebra (S ⊗[R] T) α :=
  Algebra.TensorProduct.lift
    (liftNCAlgHom
      (singleOneAlgHom.comp Algebra.TensorProduct.includeLeft)
      (of (S ⊗[R] T) α)
      (fun s a => by
        simp only [AlgHom.coe_comp, Function.comp_apply,
          Algebra.TensorProduct.includeLeft_apply, singleOneAlgHom_apply,
          of_apply, commute_iff_eq, single_mul_single, one_mul, mul_one]))
    (singleOneAlgHom.comp Algebra.TensorProduct.includeRight)
    (fun p t => by
      rw [← sum_single p, map_finsupp_sum]
      apply Commute.sum_left
      intro a _
      simp only [liftNCAlgHom, liftNCRingHom, ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe,
        AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, liftNC_single,
        AddMonoidHom.coe_coe, RingHom.coe_coe, AlgHom.coe_comp, Function.comp_apply,
        Algebra.TensorProduct.includeLeft_apply, singleOneAlgHom_apply, of_apply, single_mul_single,
        one_mul, mul_one, Algebra.TensorProduct.includeRight_apply]
      rw [commute_iff_eq]
      simp only [single_mul_single, mul_one, Algebra.TensorProduct.tmul_mul_tmul, one_mul])

lemma rTensorAlgHom_apply_single_tmul_apply
    (s : S) (a : α) (t : T) (b : α) :
    rTensorAlgHom (MonoidAlgebra.single a s ⊗ₜ[R] t) b
      = if a = b then s ⊗ₜ[R] t else 0 := by
  simp only [rTensorAlgHom, Algebra.TensorProduct.lift_tmul, AlgHom.coe_comp, Function.comp_apply,
    Algebra.TensorProduct.includeRight_apply, singleOneAlgHom_apply]
  simp only [liftNCAlgHom, liftNCRingHom, ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe,
    AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, liftNC_single,
    AddMonoidHom.coe_coe, RingHom.coe_coe, AlgHom.coe_comp, Function.comp_apply,
    Algebra.TensorProduct.includeLeft_apply, singleOneAlgHom_apply, of_apply, single_mul_single,
    one_mul, mul_one, Algebra.TensorProduct.tmul_mul_tmul]
  simp only [single_apply]

lemma rTensorAlgHom_apply_tmul_apply
    (x : MonoidAlgebra S α) (t : T) (a : α) :
    rTensorAlgHom (x ⊗ₜ[R] t) a = (x a) ⊗ₜ[R] t := by
  conv_lhs => rw [← sum_single x, Finsupp.sum, sum_tmul, map_sum]
  rw [Finset.sum_apply']
  simp_rw [rTensorAlgHom_apply_single_tmul_apply]
  simp only [Finset.sum_ite_eq', mem_support_iff, ne_eq, ite_eq_left_iff, not_not]
  intro ha; rw [ha, zero_tmul]

lemma rTensorAlgHom_toLinearMap :
    (rTensorAlgHom :
      MonoidAlgebra S α ⊗[R] T →ₐ[R] MonoidAlgebra (S ⊗[R] T) α).toLinearMap =
      (finsuppLeft _ _ _ _).toLinearMap := by
  ext x t
  apply Finsupp.ext
  intro a
  simp only [AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
    LinearMap.coe_restrictScalars, AlgHom.toLinearMap_apply]
  erw [rTensorAlgHom_apply_tmul_apply, ← finsuppLeft_apply_tmul_apply]
  rfl

lemma rTensorAlgHom_apply_eq (x : MonoidAlgebra S α ⊗[R] T) :
    rTensorAlgHom x = finsuppLeft _ _ _ _ x := by
  rw [← AlgHom.toLinearMap_apply, rTensorAlgHom_toLinearMap]
  rfl

/- -- Todo : S-linear variant
lemma rTensorAlgHom_toLinearMap' :
    (rTensorAlgHom :
      MonoidAlgebra S α ⊗[R] T →ₐ[R] MonoidAlgebra (S ⊗[R] T) α).toLinearMap =
      (finsuppLeft' _ _ _ _ _).toLinearMap := by
  ext x n
  dsimp only [AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
    LinearMap.coe_restrictScalars, AlgHom.toLinearMap_apply]
  apply Finsupp.ext
  intro a
  rw [rTensorAlgHom_apply_tmul_apply, ← finsuppLeft_apply_tmul_apply]
  rfl
-/

/-- AlgHom equiv for the tensor product of the monoid algebra with an algebra -/
noncomputable def rTensorAlgEquiv :
    (MonoidAlgebra S α) ⊗[R] T ≃ₐ[R] MonoidAlgebra (S ⊗[R] T) α := by
  apply AlgEquiv.ofLinearEquiv
    (TensorProduct.finsuppLeft R S T α :
      MonoidAlgebra S α ⊗[R] T ≃ₗ[R] (MonoidAlgebra (S ⊗[R] T) α))
  · simp only [Algebra.TensorProduct.one_def]
    apply symm
    rw [← LinearEquiv.symm_apply_eq]
    simp only [one_def]
    apply finsuppLeft_symm_apply_single
  · intro x y
    erw [← rTensorAlgHom_apply_eq]
    simp only [_root_.map_mul, rTensorAlgHom_apply_eq]
    rfl

lemma rTensorAlgEquiv_apply_eq (x : MonoidAlgebra S α ⊗[R] T) :
    rTensorAlgEquiv x = finsuppLeft R S T α x :=
  rfl

lemma rTensorAlgEquiv_apply_tmul_apply
    (x : MonoidAlgebra S α) (t : T) (a : α) :
    rTensorAlgEquiv (x ⊗ₜ[R] t) a = (x a) ⊗ₜ[R] t := by
  rw [rTensorAlgEquiv_apply_eq, finsuppLeft_apply_tmul_apply]

/-- AlgHom equiv for the tensor product of the monoid algebra with a module -/
noncomputable def scalarRTensorAlgEquiv :
    (MonoidAlgebra R α) ⊗[R] T ≃ₐ[R] MonoidAlgebra T α :=
  rTensorAlgEquiv.trans (sorry) -- algEquiv (Algebra.TensorProduct.lid R N))

end MonoidAlgebra

end TensorProduct
