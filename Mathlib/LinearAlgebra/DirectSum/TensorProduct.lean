/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Eric Wieser

! This file was ported from Lean 3 source module linear_algebra.direct_sum.tensor_product
! leanprover-community/mathlib commit 9b9d125b7be0930f564a68f1d73ace10cf46064d
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.LinearAlgebra.TensorProduct
import Mathbin.Algebra.DirectSum.Module

/-!
# Tensor products of direct sums

This file shows that taking `tensor_product`s commutes with taking `direct_sum`s in both arguments.

## Main results

* `tensor_product.direct_sum`
* `tensor_product.direct_sum_left`
* `tensor_product.direct_sum_right`
-/


section Ring

namespace TensorProduct

open TensorProduct

open DirectSum

open LinearMap

attribute [local ext] TensorProduct.ext

variable (R : Type _) [CommRing R]

variable {ι₁ : Type _} {ι₂ : Type _}

variable [DecidableEq ι₁] [DecidableEq ι₂]

variable (M₁ : ι₁ → Type _) (M₁' : Type _) (M₂ : ι₂ → Type _) (M₂' : Type _)

variable [∀ i₁, AddCommGroup (M₁ i₁)] [AddCommGroup M₁']

variable [∀ i₂, AddCommGroup (M₂ i₂)] [AddCommGroup M₂']

variable [∀ i₁, Module R (M₁ i₁)] [Module R M₁'] [∀ i₂, Module R (M₂ i₂)] [Module R M₂']

/-- The linear equivalence `(⨁ i₁, M₁ i₁) ⊗ (⨁ i₂, M₂ i₂) ≃ (⨁ i₁, ⨁ i₂, M₁ i₁ ⊗ M₂ i₂)`, i.e.
"tensor product distributes over direct sum". -/
protected def directSum :
    ((⨁ i₁, M₁ i₁) ⊗[R] ⨁ i₂, M₂ i₂) ≃ₗ[R] ⨁ i : ι₁ × ι₂, M₁ i.1 ⊗[R] M₂ i.2 :=
  by
  refine'
      LinearEquiv.ofLinear
        (lift <|
          DirectSum.toModule R _ _ fun i₁ =>
            flip <|
              DirectSum.toModule R _ _ fun i₂ =>
                flip <| curry <| DirectSum.lof R (ι₁ × ι₂) (fun i => M₁ i.1 ⊗[R] M₂ i.2) (i₁, i₂))
        (DirectSum.toModule R _ _ fun i => map (DirectSum.lof R _ _ _) (DirectSum.lof R _ _ _)) _
        _ <;>
    [ext (⟨i₁, i₂⟩x₁ x₂) : 4, ext (i₁ i₂ x₁ x₂) : 5]
  repeat'
    first
      |rw [compr₂_apply]|rw [comp_apply]|rw [id_apply]|rw [mk_apply]|rw [DirectSum.toModule_lof]|rw [map_tmul]|rw [lift.tmul]|rw [flip_apply]|rw [curry_apply]
#align tensor_product.direct_sum TensorProduct.directSum

/-- Tensor products distribute over a direct sum on the left . -/
def directSumLeft : (⨁ i₁, M₁ i₁) ⊗[R] M₂' ≃ₗ[R] ⨁ i, M₁ i ⊗[R] M₂' :=
  LinearEquiv.ofLinear
    (lift <|
      DirectSum.toModule R _ _ fun i =>
        (mk R _ _).compr₂ <| DirectSum.lof R ι₁ (fun i => M₁ i ⊗[R] M₂') _)
    (DirectSum.toModule R _ _ fun i => rtensor _ (DirectSum.lof R ι₁ _ _))
    (DirectSum.linearMap_ext R fun i =>
      TensorProduct.ext <|
        LinearMap.ext₂ fun m₁ m₂ =>
          by
          dsimp only [comp_apply, compr₂_apply, id_apply, mk_apply]
          simp_rw [DirectSum.toModule_lof, rtensor_tmul, lift.tmul, DirectSum.toModule_lof,
            compr₂_apply, mk_apply])
    (TensorProduct.ext <|
      DirectSum.linearMap_ext R fun i =>
        LinearMap.ext₂ fun m₁ m₂ =>
          by
          dsimp only [comp_apply, compr₂_apply, id_apply, mk_apply]
          simp_rw [DirectSum.toModule_lof, lift.tmul, DirectSum.toModule_lof, compr₂_apply,
            mk_apply, DirectSum.toModule_lof, rtensor_tmul])
#align tensor_product.direct_sum_left TensorProduct.directSumLeft

/-- Tensor products distribute over a direct sum on the right. -/
def directSumRight : (M₁' ⊗[R] ⨁ i, M₂ i) ≃ₗ[R] ⨁ i, M₁' ⊗[R] M₂ i :=
  TensorProduct.comm R _ _ ≪≫ₗ directSumLeft R M₂ M₁' ≪≫ₗ
    Dfinsupp.mapRange.linearEquiv fun i => TensorProduct.comm R _ _
#align tensor_product.direct_sum_right TensorProduct.directSumRight

variable {M₁ M₁' M₂ M₂'}

@[simp]
theorem directSum_lof_tmul_lof (i₁ : ι₁) (m₁ : M₁ i₁) (i₂ : ι₂) (m₂ : M₂ i₂) :
    TensorProduct.directSum R M₁ M₂ (DirectSum.lof R ι₁ M₁ i₁ m₁ ⊗ₜ DirectSum.lof R ι₂ M₂ i₂ m₂) =
      DirectSum.lof R (ι₁ × ι₂) (fun i => M₁ i.1 ⊗[R] M₂ i.2) (i₁, i₂) (m₁ ⊗ₜ m₂) :=
  by simp [TensorProduct.directSum]
#align tensor_product.direct_sum_lof_tmul_lof TensorProduct.directSum_lof_tmul_lof

@[simp]
theorem directSumLeft_tmul_lof (i : ι₁) (x : M₁ i) (y : M₂') :
    directSumLeft R M₁ M₂' (DirectSum.lof R _ _ i x ⊗ₜ[R] y) = DirectSum.lof R _ _ i (x ⊗ₜ[R] y) :=
  by
  dsimp only [direct_sum_left, LinearEquiv.ofLinear_apply, lift.tmul]
  rw [DirectSum.toModule_lof R i]
  rfl
#align tensor_product.direct_sum_left_tmul_lof TensorProduct.directSumLeft_tmul_lof

@[simp]
theorem directSumLeft_symm_lof_tmul (i : ι₁) (x : M₁ i) (y : M₂') :
    (directSumLeft R M₁ M₂').symm (DirectSum.lof R _ _ i (x ⊗ₜ[R] y)) =
      DirectSum.lof R _ _ i x ⊗ₜ[R] y :=
  by rw [LinearEquiv.symm_apply_eq, direct_sum_left_tmul_lof]
#align tensor_product.direct_sum_left_symm_lof_tmul TensorProduct.directSumLeft_symm_lof_tmul

@[simp]
theorem directSumRight_tmul_lof (x : M₁') (i : ι₂) (y : M₂ i) :
    directSumRight R M₁' M₂ (x ⊗ₜ[R] DirectSum.lof R _ _ i y) = DirectSum.lof R _ _ i (x ⊗ₜ[R] y) :=
  by
  dsimp only [direct_sum_right, LinearEquiv.trans_apply, TensorProduct.comm_tmul]
  rw [direct_sum_left_tmul_lof]
  exact Dfinsupp.mapRange_single
#align tensor_product.direct_sum_right_tmul_lof TensorProduct.directSumRight_tmul_lof

@[simp]
theorem directSumRight_symm_lof_tmul (x : M₁') (i : ι₂) (y : M₂ i) :
    (directSumRight R M₁' M₂).symm (DirectSum.lof R _ _ i (x ⊗ₜ[R] y)) =
      x ⊗ₜ[R] DirectSum.lof R _ _ i y :=
  by rw [LinearEquiv.symm_apply_eq, direct_sum_right_tmul_lof]
#align tensor_product.direct_sum_right_symm_lof_tmul TensorProduct.directSumRight_symm_lof_tmul

end TensorProduct

end Ring

