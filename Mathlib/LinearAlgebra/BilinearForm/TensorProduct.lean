/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.LinearAlgebra.BilinearForm
import Mathlib.LinearAlgebra.TensorProduct

#align_import linear_algebra.bilinear_form.tensor_product from "leanprover-community/mathlib"@"f0c8bf9245297a541f468be517f1bde6195105e9"

/-!
# The bilinear form on a tensor product

## Main definitions

* `BilinForm.tensorDistrib (B₁ ⊗ₜ B₂)`: the bilinear form on `M₁ ⊗ M₂` constructed by applying
  `B₁` on `M₁` and `B₂` on `M₂`.
* `BilinForm.tensorDistribEquiv`: `BilinForm.tensorDistrib` as an equivalence on finite free
  modules.

-/


universe u v w

variable {ι : Type*} {R : Type*} {M₁ M₂ : Type*}

open TensorProduct

namespace BilinForm

section CommSemiring

variable [CommSemiring R]

variable [AddCommMonoid M₁] [AddCommMonoid M₂]

variable [Module R M₁] [Module R M₂]

/-- The tensor product of two bilinear forms injects into bilinear forms on tensor products. -/
def tensorDistrib : BilinForm R M₁ ⊗[R] BilinForm R M₂ →ₗ[R] BilinForm R (M₁ ⊗[R] M₂) :=
  ((TensorProduct.tensorTensorTensorComm R _ _ _ _).dualMap ≪≫ₗ
    (TensorProduct.lift.equiv R _ _ _).symm ≪≫ₗ LinearMap.toBilin).toLinearMap ∘ₗ
  TensorProduct.dualDistrib R _ _ ∘ₗ
  (TensorProduct.congr (BilinForm.toLin ≪≫ₗ TensorProduct.lift.equiv R _ _ _)
    (BilinForm.toLin ≪≫ₗ TensorProduct.lift.equiv R _ _ _)).toLinearMap
#align bilin_form.tensor_distrib BilinForm.tensorDistrib

@[simp]
theorem tensorDistrib_tmul (B₁ : BilinForm R M₁) (B₂ : BilinForm R M₂) (m₁ : M₁) (m₂ : M₂)
    (m₁' : M₁) (m₂' : M₂) :
    tensorDistrib (R := R) (B₁ ⊗ₜ B₂) (m₁ ⊗ₜ m₂) (m₁' ⊗ₜ m₂') = B₁ m₁ m₁' * B₂ m₂ m₂' :=
  rfl
#align bilin_form.tensor_distrib_tmul BilinForm.tensorDistrib_tmul

/-- The tensor product of two bilinear forms, a shorthand for dot notation. -/
@[reducible]
protected def tmul (B₁ : BilinForm R M₁) (B₂ : BilinForm R M₂) : BilinForm R (M₁ ⊗[R] M₂) :=
  tensorDistrib (R := R) (B₁ ⊗ₜ[R] B₂)
#align bilin_form.tmul BilinForm.tmul

end CommSemiring

section CommRing

variable [CommRing R]

variable [AddCommGroup M₁] [AddCommGroup M₂]

variable [Module R M₁] [Module R M₂]

variable [Module.Free R M₁] [Module.Finite R M₁]

variable [Module.Free R M₂] [Module.Finite R M₂]

variable [Nontrivial R]

/-- `tensorDistrib` as an equivalence. -/
noncomputable def tensorDistribEquiv :
    BilinForm R M₁ ⊗[R] BilinForm R M₂ ≃ₗ[R] BilinForm R (M₁ ⊗[R] M₂) :=
  -- the same `LinearEquiv`s as from `tensorDistrib`,
  -- but with the inner linear map also as an equiv
  TensorProduct.congr (BilinForm.toLin ≪≫ₗ TensorProduct.lift.equiv R _ _ _)
    (BilinForm.toLin ≪≫ₗ TensorProduct.lift.equiv R _ _ _) ≪≫ₗ
  TensorProduct.dualDistribEquiv R (M₁ ⊗ M₁) (M₂ ⊗ M₂) ≪≫ₗ
  (TensorProduct.tensorTensorTensorComm R _ _ _ _).dualMap ≪≫ₗ
  (TensorProduct.lift.equiv R _ _ _).symm ≪≫ₗ LinearMap.toBilin
#align bilin_form.tensor_distrib_equiv BilinForm.tensorDistribEquiv

@[simp]
theorem tensorDistribEquiv_apply (B : BilinForm R M₁ ⊗ BilinForm R M₂) :
    tensorDistribEquiv (R := R) (M₁ := M₁) (M₂ := M₂) B = tensorDistrib (R := R) B :=
  rfl
#align bilin_form.tensor_distrib_equiv_apply BilinForm.tensorDistribEquiv_apply

end CommRing

end BilinForm
