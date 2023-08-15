/-
Copyright (c) 2023 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import Mathlib.LinearAlgebra.TensorProduct
import Mathlib.RingTheory.TensorProduct

/-! # Structure of A ⊗[R] B module on a tensor product -/


variable {R A B : Type*} [CommSemiring R] [Ring A] [Ring B]
  [Algebra R A] [Algebra R B]
  {M N : Type*} [AddCommMonoid M] [AddCommMonoid N]
  [Module R M] [Module A M] [IsScalarTower R A M]
  [Module R N] [Module B N] [IsScalarTower R B N]

open scoped TensorProduct

def toFun_aux (a : A) (b : B) : M ⊗[R] N →ₗ[R] M ⊗[R] N := by
  apply TensorProduct.lift
  apply LinearMap.mk₂ R (fun m n ↦ (a • m) ⊗ₜ[R] (b • n))
  · intro m m' n
    simp only [smul_add, TensorProduct.add_tmul]
  · intro r m n
    rw [TensorProduct.smul_tmul', smul_algebra_smul_comm]
  · intro m n n'
    simp only [smul_add, TensorProduct.tmul_add]
  · intro r m n
    rw [← TensorProduct.tmul_smul r, smul_algebra_smul_comm]

@[simp]
def toFun_aux_apply (a : A) (b: B) (m : M) (n : N) :
    toFun_aux a b (m ⊗ₜ[R] n) = (a • m) ⊗ₜ[R] (b • n) := rfl

def TensorProduct.moduleMap' : (A ⊗[R] B) →ₗ[R] (M ⊗[R] N) →ₗ[R] (M ⊗[R] N) := by
  apply TensorProduct.lift
  apply LinearMap.mk₂ R toFun_aux
  · intro a a' b
    apply TensorProduct.ext'
    intro m n
    simp only [toFun_aux_apply, LinearMap.add_apply, add_smul, TensorProduct.add_tmul]
  · intro r a b
    apply TensorProduct.ext'
    intro m n
    simp only [toFun_aux_apply, smul_assoc, LinearMap.smul_apply, TensorProduct.smul_tmul']
  · intro a b b'
    apply TensorProduct.ext'
    intro m n
    simp only [toFun_aux_apply, LinearMap.add_apply, add_smul, TensorProduct.tmul_add]
  · intro r a b
    apply TensorProduct.ext'
    intro m n
    simp only [toFun_aux_apply, smul_assoc, TensorProduct.tmul_smul, LinearMap.smul_apply]

def Algebra.TensorProduct.moduleMap : (A ⊗[R] B) →ₐ[R] (M ⊗[R] N) →ₗ[R] (M ⊗[R] N) := by
  apply Algebra.TensorProduct.algHomOfLinearMapTensorProduct
    (TensorProduct.moduleMap') -- (TensorProduct.moduleMap' R A B M N)
  · intro a a' b b'
    simp only [TensorProduct.moduleMap', TensorProduct.lift.tmul, LinearMap.mk₂_apply]
    apply _root_.TensorProduct.ext'
    intro m n
    simp only [toFun_aux_apply, LinearMap.mul_apply, mul_smul]
  · intro r
    simp only [TensorProduct.moduleMap', TensorProduct.lift.tmul, LinearMap.mk₂_apply]
    apply _root_.TensorProduct.ext'
    intro m n
    simp only [toFun_aux_apply, algebraMap_smul, one_smul, Module.algebraMap_end_apply]
    exact rfl

variable (a : A) (b : B) (x : A ⊗[R] B)

#check TensorProduct.moduleMap' (a ⊗ₜ[R] b)

#check Algebra.TensorProduct.moduleMap.toFun (a ⊗ₜ[R] b)

lemma Algebra.TensorProduct.moduleMap_apply (a : A) (b : B) (m : M) (n : N) :
  Algebra.TensorProduct.moduleMap.toFun (a ⊗ₜ[R] b) (m ⊗ₜ[R] n) = (a • m) ⊗ₜ[R] (b • n) := rfl

example (a : A) (b : B) (m : M) (n : N) :
  Algebra.TensorProduct.moduleMap.toFun (a ⊗ₜ[R] b) (m ⊗ₜ[R] n) = (a • m) ⊗ₜ[R] (b • n) := rfl
