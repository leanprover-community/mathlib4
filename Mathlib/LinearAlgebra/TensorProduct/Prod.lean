/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.Prod
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Tensor products of products

This file shows that taking `TensorProduct`s commutes with taking `Prod`s in both arguments.

## Main results

* `TensorProduct.prodLeft`
* `TensorProduct.prodRight`

## Notes

See `Mathlib/LinearAlgebra/TensorProduct/Pi.lean` for arbitrary products.

-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

variable (R S M₁ M₂ M₃ : Type*)

namespace TensorProduct

variable [CommSemiring R] [Semiring S] [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]
variable [Algebra R S]
variable [Module R M₁] [Module S M₁] [IsScalarTower R S M₁] [Module R M₂] [Module R M₃]

attribute [ext] TensorProduct.ext

/-- Tensor products distribute over a product on the right. -/
def prodRight : M₁ ⊗[R] (M₂ × M₃) ≃ₗ[S] (M₁ ⊗[R] M₂) × (M₁ ⊗[R] M₃) :=
  LinearEquiv.ofLinear
    (TensorProduct.AlgebraTensorModule.lift <|
      LinearMap.prodMapLinear R M₂ M₃ (M₁ ⊗[R] M₂) (M₁ ⊗[R] M₃) S ∘ₗ
        LinearMap.prod (AlgebraTensorModule.mk R S M₁ M₂) (AlgebraTensorModule.mk R S M₁ M₃))
    (LinearMap.coprod
      (AlgebraTensorModule.lTensor _ _ <| LinearMap.inl _ _ _)
      (AlgebraTensorModule.lTensor _ _ <| LinearMap.inr _ _ _))
    (by ext <;> simp)
    (by ext <;> simp)

@[simp] theorem prodRight_tmul (m₁ : M₁) (m : M₂ × M₃) :
    prodRight R S M₁ M₂ M₃ (m₁ ⊗ₜ m) = (m₁ ⊗ₜ m.1, m₁ ⊗ₜ m.2) :=
  rfl

@[simp] theorem prodRight_symm_tmul (m₁ : M₁) (m₂ : M₂) (m₃ : M₃) :
    (prodRight R S M₁ M₂ M₃).symm (m₁ ⊗ₜ m₂, m₁ ⊗ₜ m₃) = (m₁ ⊗ₜ (m₂, m₃)) :=
  (LinearEquiv.symm_apply_eq _).mpr rfl

variable [Module S M₂] [IsScalarTower R S M₂]

/-- Tensor products distribute over a product on the left . -/
def prodLeft : (M₁ × M₂) ⊗[R] M₃ ≃ₗ[S] (M₁ ⊗[R] M₃) × (M₂ ⊗[R] M₃) :=
  AddEquiv.toLinearEquiv (TensorProduct.comm _ _ _ ≪≫ₗ
      TensorProduct.prodRight R R _ _ _ ≪≫ₗ
      (TensorProduct.comm R _ _).prodCongr (TensorProduct.comm R _ _)).toAddEquiv
    fun c x ↦ x.induction_on (by simp) (by simp [TensorProduct.smul_tmul']) (by simp_all)

@[simp] theorem prodLeft_tmul (m₁ : M₁) (m₂ : M₂) (m₃ : M₃) :
    prodLeft R S M₁ M₂ M₃ ((m₁, m₂) ⊗ₜ m₃) = (m₁ ⊗ₜ m₃, m₂ ⊗ₜ m₃) :=
  rfl

@[simp] theorem prodLeft_symm_tmul (m₁ : M₁) (m₂ : M₂) (m₃ : M₃) :
    (prodLeft R S M₁ M₂ M₃).symm (m₁ ⊗ₜ m₃, m₂ ⊗ₜ m₃) = ((m₁, m₂) ⊗ₜ m₃) :=
  (LinearEquiv.symm_apply_eq _).mpr rfl

end TensorProduct
